#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
OFERTAS CAROCA: ofertas reales + códigos de descuento (estilo Knasta) para tiendas chilenas.

1) Guarda el historial de precios de cada producto (un registro por cambio de precio).
2) Solo avisa cuando el precio de HOY está muy por debajo del precio habitual
   (mediana de los últimos días), no contra el "precio normal" que muestra la tienda.
3) Compara con otras tiendas cuando el producto tiene código de barras (EAN).
4) Revisa las páginas de cada tienda buscando códigos/cupones de descuento nuevos.

Todo se configura en tiendas.yml. Modo diagnóstico: MODO=diagnostico.
"""
import gzip
import json
import os
import re
import smtplib
import sqlite3
import statistics
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import date, datetime, timedelta, timezone
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from html import escape, unescape
from urllib.parse import quote_plus, urljoin

import requests
import yaml

AQUI = os.path.dirname(os.path.abspath(__file__))
CONFIG = os.environ.get("CONFIG", os.path.join(AQUI, "tiendas.yml"))
DB_PATH = os.environ.get("DB", "datos/precios.db")
MODO = os.environ.get("MODO", "normal").strip().lower()
CHILE = timezone(timedelta(hours=-3))
INICIO = time.time()

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/130.0 Safari/537.36")
S = requests.Session()
S.headers.update({"User-Agent": UA, "Accept-Language": "es-CL,es;q=0.9",
                  "Accept": "text/html,application/json;q=0.9,*/*;q=0.8"})

CFG = {}
FIN_GLOBAL = INICIO + 18 * 60
FIN_TIENDA = FIN_GLOBAL

DEFAULTS = {
    "umbral_oferta": 0.40, "umbral_error": 0.65, "min_dias_historial": 7,
    "ventana_dias": 60, "precio_minimo": 15000, "avisar_sin_historial": False,
    "umbral_sin_historial": 0.60, "incluir_precio_tarjeta": False,
    "no_repetir_dias": 7, "minutos_max": 18, "max_ofertas_correo": 40,
    "buscar_codigos": True, "excluir": [], "busquedas": [],
}


# ----------------------------------------------------------------- utilidades
def log(*a):
    print(datetime.now(CHILE).strftime("%H:%M:%S"), *a, flush=True)


def quedan(seg=0):
    return time.time() < min(FIN_GLOBAL, FIN_TIENDA) - seg


def get(url, params=None, intentos=2):
    for i in range(intentos):
        try:
            r = S.get(url, params=params, timeout=25)
            if r.status_code in (429, 503) and i + 1 < intentos:
                time.sleep(5 * (i + 1))
                continue
            return r
        except requests.RequestException as e:
            if i + 1 == intentos:
                log("   error", url[:90], type(e).__name__)
            time.sleep(2)
    return None


def num(v):
    """'19.990', '$ 19.990', '19990.00', 19990 -> 19990.0"""
    if v is None or isinstance(v, bool):
        return None
    if isinstance(v, (int, float)):
        return float(v) if v > 0 else None
    s = re.sub(r"[^\d.,]", "", str(v))
    if not s:
        return None
    if re.fullmatch(r"\d{1,3}([.,]\d{3})+", s):
        s = re.sub(r"[.,]", "", s)
    elif "," in s and "." in s:
        if s.rfind(",") > s.rfind("."):
            s = s.replace(".", "").replace(",", ".")
        else:
            s = s.replace(",", "")
    else:
        s = s.replace(",", ".")
    try:
        f = float(s)
        return f if f > 0 else None
    except ValueError:
        return None


def limpiar_ean(e):
    d = re.sub(r"\D", "", str(e or "")).lstrip("0")
    return d if len(d) >= 7 else None


def clp(v):
    return "$" + f"{int(round(v)):,}".replace(",", ".") if v else "-"


# ---------------------------------------------------------------- base datos
def abrir_db():
    os.makedirs(os.path.dirname(DB_PATH) or ".", exist_ok=True)
    db = sqlite3.connect(DB_PATH)
    db.executescript("""
    CREATE TABLE IF NOT EXISTS productos(id TEXT PRIMARY KEY, tienda TEXT, nombre TEXT,
        marca TEXT, url TEXT, imagen TEXT, ean TEXT, primer_dia TEXT, ultimo_dia TEXT,
        precio REAL, lista REAL, stock INTEGER);
    CREATE TABLE IF NOT EXISTS precios(id TEXT, dia TEXT, precio REAL, PRIMARY KEY(id, dia));
    CREATE TABLE IF NOT EXISTS avisos(id TEXT, dia TEXT, precio REAL);
    CREATE TABLE IF NOT EXISTS estado(clave TEXT PRIMARY KEY, valor TEXT);
    CREATE TABLE IF NOT EXISTS urls(tienda TEXT, url TEXT, PRIMARY KEY(tienda, url));
    CREATE TABLE IF NOT EXISTS codigos(tienda TEXT, codigo TEXT, primer_dia TEXT,
        ultimo_dia TEXT, texto TEXT, PRIMARY KEY(tienda, codigo));
    CREATE INDEX IF NOT EXISTS ix_ean ON productos(ean);
    """)
    return db


def estado(db, k, v=None):
    if v is None:
        r = db.execute("SELECT valor FROM estado WHERE clave=?", (k,)).fetchone()
        return r[0] if r else None
    db.execute("INSERT OR REPLACE INTO estado VALUES(?,?)", (k, str(v)))


def registrar(db, tienda, pid, p, hoy):
    ant = db.execute("SELECT precio FROM precios WHERE id=? AND dia<? ORDER BY dia DESC LIMIT 1",
                     (pid, hoy)).fetchone()
    if ant is None or abs(ant[0] - p["precio"]) > 0.5:
        db.execute("INSERT OR REPLACE INTO precios VALUES(?,?,?)", (pid, hoy, p["precio"]))
    else:  # mismo precio que el último registrado: no hace falta fila nueva
        db.execute("DELETE FROM precios WHERE id=? AND dia=?", (pid, hoy))
    db.execute("""INSERT INTO productos VALUES(?,?,?,?,?,?,?,?,?,?,?,?)
        ON CONFLICT(id) DO UPDATE SET nombre=excluded.nombre, marca=excluded.marca,
        url=excluded.url, imagen=COALESCE(excluded.imagen, imagen),
        ean=COALESCE(excluded.ean, ean), ultimo_dia=excluded.ultimo_dia,
        precio=excluded.precio, lista=excluded.lista, stock=excluded.stock""",
               (pid, tienda, p.get("nombre"), p.get("marca"), p.get("url"), p.get("imagen"),
                p.get("ean"), hoy, hoy, p["precio"], p.get("lista"), 1 if p.get("stock") else 0))


def historial(db, pid, hoy):
    """Precio de cada día (sin contar hoy) dentro de la ventana."""
    fila = db.execute("SELECT primer_dia FROM productos WHERE id=?", (pid,)).fetchone()
    if not fila:
        return []
    d_hoy = date.fromisoformat(hoy)
    d = max(date.fromisoformat(fila[0]), d_hoy - timedelta(days=CFG["ventana_dias"]))
    rows = db.execute("SELECT dia, precio FROM precios WHERE id=? AND dia<? ORDER BY dia",
                      (pid, hoy)).fetchall()
    serie, i, actual = [], 0, None
    while d < d_hoy:
        ds = d.isoformat()
        while i < len(rows) and rows[i][0] <= ds:
            actual = rows[i][1]
            i += 1
        if actual is not None:
            serie.append(actual)
        d += timedelta(days=1)
    return serie


def evaluar(db, pid, p, hoy):
    serie = historial(db, pid, hoy)
    if len(serie) >= CFG["min_dias_historial"]:
        ref = statistics.median(serie)
        desc = 1 - p["precio"] / ref
        if desc >= CFG["umbral_oferta"]:
            tipo = "POSIBLE ERROR DE PRECIO" if desc >= CFG["umbral_error"] else "Oferta real"
            return dict(tipo=tipo, ref=ref, minimo=min(serie), desc=desc, dias=len(serie))
    elif CFG["avisar_sin_historial"] and p.get("lista"):
        desc = 1 - p["precio"] / p["lista"]
        if desc >= CFG["umbral_sin_historial"]:
            return dict(tipo="Sin historial aún (verificar)", ref=p["lista"], minimo=None,
                        desc=desc, dias=len(serie))
    return None


def ya_avisado(db, pid, precio, hoy):
    desde = (date.fromisoformat(hoy) - timedelta(days=CFG["no_repetir_dias"])).isoformat()
    r = db.execute("SELECT MIN(precio) FROM avisos WHERE id=? AND dia>=?", (pid, desde)).fetchone()
    return r[0] is not None and precio >= r[0] * 0.97


def otras_tiendas(db, pid, ean, hoy):
    if not ean:
        return []
    desde = (date.fromisoformat(hoy) - timedelta(days=2)).isoformat()
    return db.execute("""SELECT tienda, precio, url FROM productos WHERE ean=? AND id<>?
        AND stock=1 AND ultimo_dia>=? ORDER BY precio LIMIT 3""", (ean, pid, desde)).fetchall()


def limpiar_db(db, hoy):
    d = date.fromisoformat(hoy)
    c60 = (d - timedelta(days=60)).isoformat()
    c120 = (d - timedelta(days=120)).isoformat()
    db.execute("DELETE FROM precios WHERE id IN (SELECT id FROM productos WHERE ultimo_dia<?)", (c60,))
    db.execute("DELETE FROM productos WHERE ultimo_dia<?", (c60,))
    db.execute("""DELETE FROM precios WHERE dia<? AND EXISTS (SELECT 1 FROM precios p2
        WHERE p2.id=precios.id AND p2.dia>precios.dia AND p2.dia<=?)""", (c120, c60))
    db.execute("DELETE FROM avisos WHERE dia<?", (c60,))


# ----------------------------------------------------------------- lectores
def lector_vtex(t, db):
    base = t["url"].rstrip("/")
    for q in t.get("busquedas") or [None]:  # sin búsquedas: todo el catálogo, mayor descuento primero
        for pg in range(t.get("paginas", 10)):
            if not quedan():
                return
            params = {"_from": pg * 50, "_to": pg * 50 + 49, "O": "OrderByBestDiscountDESC"}
            if q:
                params["ft"] = q
            r = get(base + "/api/catalog_system/pub/products/search", params)
            if r is None or r.status_code not in (200, 206):
                break
            try:
                data = r.json()
            except ValueError:
                break
            if not isinstance(data, list) or not data:
                break
            for prod in data:
                for it in prod.get("items") or []:
                    sellers = it.get("sellers") or []
                    sel = next((s for s in sellers if s.get("sellerDefault")), sellers[0] if sellers else None)
                    if not sel:
                        continue
                    of = sel.get("commertialOffer") or {}
                    imgs = it.get("images") or []
                    yield dict(sku=it.get("itemId"), nombre=it.get("nameComplete") or prod.get("productName"),
                               marca=prod.get("brand"), url=prod.get("link"),
                               imagen=imgs[0].get("imageUrl") if imgs else None, ean=it.get("ean"),
                               precio=num(of.get("Price")), lista=num(of.get("ListPrice")),
                               stock=(of.get("AvailableQuantity") or 0) > 0)
            time.sleep(0.5)


def lector_shopify(t, db):
    base = t["url"].rstrip("/")
    for pg in range(1, t.get("paginas", 20) + 1):
        if not quedan():
            return
        r = get(base + "/products.json", {"limit": 250, "page": pg})
        if r is None or r.status_code != 200:
            break
        try:
            prods = r.json().get("products") or []
        except ValueError:
            break
        if not prods:
            break
        for pr in prods:
            imgs = pr.get("images") or []
            for v in pr.get("variants") or []:
                extra = "" if v.get("title") in (None, "Default Title") else f" - {v['title']}"
                yield dict(sku=v.get("id"), nombre=(pr.get("title") or "") + extra, marca=pr.get("vendor"),
                           url=f"{base}/products/{pr.get('handle')}?variant={v.get('id')}",
                           imagen=imgs[0].get("src") if imgs else None, ean=v.get("barcode"),
                           precio=num(v.get("price")), lista=num(v.get("compare_at_price")),
                           stock=v.get("available", True))
        time.sleep(0.5)


def lector_falabella(t, db):
    """Falabella, Sodimac, Tottus (misma plataforma). Lee el JSON de las páginas de búsqueda."""
    base = t["url"].rstrip("/")
    plantillas = list(t.get("listados") or [])
    for q in t.get("busquedas") or CFG["busquedas"]:
        plantillas.append(f"{base}/search?Ntt={quote_plus(q)}&page={{page}}")
    for pl in plantillas:
        for pg in range(1, t.get("paginas", 2) + 1):
            if not quedan():
                return
            u = pl.replace("{page}", str(pg)) if "{page}" in pl else pl + ("&" if "?" in pl else "?") + f"page={pg}"
            r = get(u)
            if r is None or r.status_code != 200:
                break
            m = re.search(r'<script id="__NEXT_DATA__"[^>]*>(.*?)</script>', r.text, re.S)
            if not m:
                break
            try:
                res = json.loads(m.group(1))["props"]["pageProps"].get("results") or []
            except (ValueError, KeyError, TypeError, AttributeError):
                break
            if not res:
                break
            for x in res:
                precios = {}
                for pr in x.get("prices") or []:
                    v = pr.get("price")
                    v = v[0] if isinstance(v, list) and v else v
                    if num(v):
                        precios[str(pr.get("type") or "")] = num(v)
                if not precios:
                    continue
                cands = [v for k, v in precios.items() if "cmr" not in k.lower()]
                if CFG["incluir_precio_tarjeta"] or not cands:
                    cands = list(precios.values())
                media = x.get("mediaUrls") or []
                yield dict(sku=x.get("skuId") or x.get("productId"), nombre=x.get("displayName"),
                           marca=x.get("brand"), url=x.get("url"), imagen=media[0] if media else None,
                           ean=None, precio=min(cands),
                           lista=precios.get("normalPrice") or max(precios.values()), stock=True)
            time.sleep(1)


def _productos_ld(d):
    if isinstance(d, list):
        for x in d:
            yield from _productos_ld(x)
    elif isinstance(d, dict):
        tipo = d.get("@type")
        tipos = tipo if isinstance(tipo, list) else [tipo]
        if "Product" in tipos:
            yield d
        for k in ("@graph", "mainEntity", "hasVariant"):
            if k in d:
                yield from _productos_ld(d[k])


def _desde_ld(d, url):
    ofs = d.get("offers")
    if isinstance(ofs, dict) and ofs.get("offers"):
        ofs = ofs["offers"]
    ofs = ofs if isinstance(ofs, list) else ([ofs] if ofs else [])
    mejor, lista = None, None
    for o in ofs:
        if not isinstance(o, dict):
            continue
        precio = num(o.get("price") or o.get("lowPrice"))
        specs = o.get("priceSpecification") or []
        specs = specs if isinstance(specs, list) else [specs]
        for sp in specs:
            if not isinstance(sp, dict):
                continue
            tipo = str(sp.get("priceType", ""))
            if re.search(r"ListPrice|Strikethrough|MSRP", tipo, re.I):
                lista = num(sp.get("price")) or lista
            elif precio is None:
                precio = num(sp.get("price"))
        stock = not re.search(r"OutOfStock|SoldOut|Discontinued", str(o.get("availability", "")), re.I)
        if precio and (mejor is None or precio < mejor[0]):
            mejor = (precio, stock)
    if not mejor:
        return None
    img = d.get("image")
    if isinstance(img, list):
        img = img[0] if img else None
    if isinstance(img, dict):
        img = img.get("url")
    marca = d.get("brand")
    if isinstance(marca, dict):
        marca = marca.get("name")
    ean = d.get("gtin13") or d.get("gtin") or d.get("gtin12") or d.get("gtin14") or d.get("gtin8")
    return dict(sku=d.get("sku") or d.get("productID") or url, nombre=unescape(str(d.get("name") or "")),
                marca=marca, url=d.get("url") or url, imagen=img, ean=ean,
                precio=mejor[0], lista=lista, stock=mejor[1])


def extraer_jsonld(html, url):
    for m in re.finditer(r'<script[^>]*application/ld\+json[^>]*>(.*?)</script>', html, re.S | re.I):
        try:
            data = json.loads(m.group(1).strip())
        except ValueError:
            continue
        for prod in _productos_ld(data):
            p = _desde_ld(prod, url)
            if p:
                return p
    m = re.search(r'(?:product|og):price:amount["\'][^>]*content=["\']([^"\']+)', html)
    t = re.search(r'og:title["\'][^>]*content=["\']([^"\']+)', html)
    if m and t:
        return dict(sku=url, nombre=unescape(t.group(1)), url=url, precio=num(m.group(1)),
                    lista=None, stock=not re.search(r"out of stock|agotado", html[:200000], re.I))
    return None


def urls_sitemap(t):
    base = t["url"].rstrip("/")
    pend = [t["sitemap"]] if t.get("sitemap") else []
    if not pend:
        r = get(base + "/robots.txt", intentos=1)
        if r is not None and r.status_code == 200:
            pend = re.findall(r"(?im)^sitemap:\s*(\S+)", r.text)
        pend = pend or [base + "/sitemap.xml"]
    patron = re.compile(t.get("patron_producto") or r"/p/|/product|/producto|\.html$|/\d{6,}", re.I)
    vistos, encontrados = set(), []
    while pend and len(vistos) < 150 and len(encontrados) < t.get("max_urls", 40000):
        sm = pend.pop(0)
        if sm in vistos:
            continue
        vistos.add(sm)
        r = get(sm, intentos=1)
        if r is None or r.status_code != 200:
            continue
        cont = r.content
        if cont[:2] == b"\x1f\x8b":
            try:
                cont = gzip.decompress(cont)
            except OSError:
                continue
        indice = b"<sitemapindex" in cont[:3000]
        todo_producto = re.search(r"product|producto|pdp", sm, re.I)
        for loc in re.findall(rb"<loc>\s*(.*?)\s*</loc>", cont, re.S):
            u = unescape(loc.decode("utf-8", "ignore")).strip()
            if indice:
                if re.search(r"product|producto|pdp", u, re.I):
                    pend.insert(0, u)
                elif not re.search(r"blog|categor|brand|marca|page|static|image", u, re.I):
                    pend.append(u)
            elif todo_producto or patron.search(u):
                encontrados.append(u)
    return encontrados


def lector_jsonld(t, db):
    """Lector universal: lee el sitemap de la tienda y revisa N productos por pasada (rotando)."""
    tid = t["id"]
    hoy = date.today()
    ult = estado(db, f"urls_dia:{tid}")
    n = db.execute("SELECT COUNT(*) FROM urls WHERE tienda=?", (tid,)).fetchone()[0]
    if not n or not ult or (hoy - date.fromisoformat(ult)).days >= 7:
        lst = urls_sitemap(t)
        log(f"   sitemap: {len(lst)} productos")
        if lst:
            db.execute("DELETE FROM urls WHERE tienda=?", (tid,))
            db.executemany("INSERT OR IGNORE INTO urls VALUES(?,?)", [(tid, u) for u in lst])
            estado(db, f"urls_dia:{tid}", hoy.isoformat())
            db.commit()
    todas = [r[0] for r in db.execute("SELECT url FROM urls WHERE tienda=? ORDER BY url", (tid,))]
    if not todas:
        return
    cursor = int(estado(db, f"cursor:{tid}") or 0) % len(todas)
    tam = 15 if MODO == "diagnostico" else t.get("max_productos", 300)
    lote = (todas[cursor:] + todas[:cursor])[:tam]

    def bajar(u):
        if not quedan(45):
            return ("tiempo", None)
        r = get(u, intentos=1)
        if r is None or r.status_code != 200:
            return ("ok", None)
        return ("ok", extraer_jsonld(r.text, u))

    hechos = 0
    with ThreadPoolExecutor(t.get("hilos", 4)) as ex:
        for st, p in ex.map(bajar, lote):
            if st == "tiempo":
                continue
            hechos += 1
            if p:
                yield p
    estado(db, f"cursor:{tid}", (cursor + hechos) % len(todas))


LECTORES = {"vtex": lector_vtex, "shopify": lector_shopify,
            "falabella": lector_falabella, "jsonld": lector_jsonld}


def detectar(t, db, forzar=False):
    clave = f"tipo:{t['id']}"
    if not forzar and estado(db, clave):
        return estado(db, clave)
    base = t["url"].rstrip("/")
    tipo = "jsonld"
    r = get(base + "/products.json", {"limit": 1}, intentos=1)
    if r is not None and r.status_code == 200 and '"products"' in r.text[:300]:
        tipo = "shopify"
    else:
        r = get(base + "/api/catalog_system/pub/products/search", {"_from": 0, "_to": 0}, intentos=1)
        if r is not None and r.status_code in (200, 206) and r.text.lstrip().startswith("[{"):
            tipo = "vtex"
    estado(db, clave, tipo)
    return tipo


# ------------------------------------------------------- códigos de descuento
RE_CODIGO = re.compile(
    r"(?:c[oó]digo|cup[oó]n|code|usa(?:ndo)?\s+el|ingresa)\s*(?:de\s+descuento|promocional)?\s*"
    r"[:\-–]?\s*[\"'“”«»]?\s*([A-Z][A-Z0-9]{3,19}|[0-9]{2,}[A-Z][A-Z0-9]{2,17})\b")
NO_CODIGO = {"DESCUENTO", "PROMOCIONAL", "PROMOCION", "VALIDO", "VÁLIDO", "CUPON", "CUPÓN",
             "CODIGO", "CÓDIGO", "AQUI", "AQUÍ", "COMPRA", "COMPRAS", "TIENDA", "ONLINE",
             "DESPACHO", "GRATIS", "TODO", "TODOS", "ENVIO", "ENVÍO", "PARA", "CON", "SKU",
             "HTML", "HTTP", "HTTPS", "JSON", "NULL", "TRUE", "FALSE", "UTF", "POSTAL", "QR"}


def texto_plano(html):
    html = re.sub(r"(?is)<(script|style|noscript|svg)[^>]*>.*?</\1>", " ", html)
    return re.sub(r"\s+", " ", unescape(re.sub(r"<[^>]+>", " ", html)))


def buscar_codigos(t, db, hoy):
    paginas = [t["url"]] + list(t.get("paginas_codigos") or [])
    nuevos = []
    for u in paginas:
        r = get(u, intentos=1)
        if r is None or r.status_code != 200:
            continue
        txt = texto_plano(r.text)
        for m in RE_CODIGO.finditer(txt):
            cod = m.group(1).upper()
            if cod in NO_CODIGO or len(cod) < 4:
                continue
            ctx = txt[max(0, m.start() - 90): m.end() + 90].strip()
            if not re.search(r"%|\$|dcto|descuento|off|gratis|env[ií]o", ctx, re.I):
                continue  # sin pinta de promoción
            existe = db.execute("SELECT 1 FROM codigos WHERE tienda=? AND codigo=?",
                                (t["nombre"], cod)).fetchone()
            if existe:
                db.execute("UPDATE codigos SET ultimo_dia=? WHERE tienda=? AND codigo=?",
                           (hoy, t["nombre"], cod))
            else:
                db.execute("INSERT INTO codigos VALUES(?,?,?,?,?)", (t["nombre"], cod, hoy, hoy, ctx))
                nuevos.append(dict(tienda=t["nombre"], codigo=cod, texto=ctx, url=u))
    return nuevos


# ---------------------------------------------------------------------- correo
def enviar(asunto, html):
    u = os.environ.get("EMAIL_USER")
    pw = os.environ.get("EMAIL_PASSWORD")
    to = os.environ.get("EMAIL_TO") or u
    if not (u and pw):
        log("Sin credenciales de correo; muestro el asunto:", asunto)
        return
    msg = MIMEMultipart("alternative")
    msg["Subject"], msg["From"], msg["To"] = asunto, u, to
    msg.attach(MIMEText(html, "html", "utf-8"))
    with smtplib.SMTP_SSL(os.environ.get("SMTP_HOST", "smtp.gmail.com"), 465) as s:
        s.login(u, pw)
        s.sendmail(u, [x.strip() for x in to.split(",")], msg.as_string())
    log("Correo enviado:", asunto)


def html_correo(ofertas, codigos, resumen, titulo):
    h = [f'<div style="font-family:Arial,sans-serif;max-width:640px;margin:auto">'
         f'<h2 style="margin:8px 0">{escape(titulo)}</h2>']
    if codigos:
        h.append('<h3 style="margin:16px 0 6px">🎟️ Códigos de descuento nuevos</h3>')
        for c in codigos:
            h.append(f'<div style="border:1px dashed #e67e22;border-radius:8px;padding:10px;margin:6px 0">'
                     f'<b style="font-size:18px">{escape(c["codigo"])}</b> · {escape(c["tienda"])}<br>'
                     f'<span style="color:#555;font-size:13px">…{escape(c["texto"])}…</span><br>'
                     f'<a href="{escape(c["url"])}">Ver tienda</a></div>')
    if ofertas:
        h.append('<h3 style="margin:16px 0 6px">🔥 Ofertas reales</h3>')
    for o in ofertas:
        color = "#c0392b" if "ERROR" in o["tipo"] else "#27ae60"
        img = f'<img src="{escape(o["imagen"])}" width="90" style="float:left;margin-right:10px;border-radius:6px">' if o.get("imagen") else ""
        hist = (f'Precio habitual ({o["dias"]} días): <s>{clp(o["ref"])}</s> · mínimo previo {clp(o["minimo"])}'
                if o.get("minimo") else f'Precio "normal" de la tienda: <s>{clp(o["ref"])}</s>')
        otras = ""
        if o.get("otras"):
            otras = "<br>Otras tiendas: " + " · ".join(
                f'<a href="{escape(u or "")}">{escape(ti.split(":")[0])} {clp(pr)}</a>' for ti, pr, u in o["otras"])
        tarjeta = f' · lista tienda {clp(o["lista"])}' if o.get("lista") and o.get("minimo") else ""
        h.append(f'<div style="border:1px solid #ddd;border-radius:8px;padding:10px;margin:8px 0;overflow:hidden">{img}'
                 f'<span style="background:{color};color:#fff;padding:2px 6px;border-radius:4px;font-size:12px">'
                 f'{escape(o["tipo"])} -{o["desc"]*100:.0f}%</span><br>'
                 f'<b>{escape(o.get("nombre") or "")}</b><br>{escape(o["tienda"])}'
                 f'{" · " + escape(str(o["marca"])) if o.get("marca") else ""}<br>'
                 f'<span style="font-size:20px;color:{color}"><b>{clp(o["precio"])}</b></span><br>'
                 f'<span style="font-size:13px;color:#555">{hist}{tarjeta}{otras}</span><br>'
                 f'<a href="{escape(o.get("url") or "")}">Ver producto</a></div>')
    if resumen:
        h.append('<h3 style="margin:16px 0 6px">Estado de las tiendas</h3><table style="font-size:13px;border-collapse:collapse">')
        for nombre, tipo, n, err in resumen:
            est = "✅" if n else "⚠️"
            h.append(f'<tr><td style="padding:2px 8px">{est} {escape(nombre)}</td><td style="padding:2px 8px">{tipo}</td>'
                     f'<td style="padding:2px 8px">{n} productos</td><td style="padding:2px 8px;color:#c0392b">{escape(err or "")}</td></tr>')
        h.append("</table>")
    h.append('<p style="color:#888;font-size:12px">Verifica siempre el precio final en el carro antes de comprar.</p></div>')
    return "".join(h)


# ------------------------------------------------------------------------ main
def main():
    global CFG, FIN_GLOBAL, FIN_TIENDA
    with open(CONFIG, encoding="utf-8") as f:
        CFG = {**DEFAULTS, **(yaml.safe_load(f) or {})}
    FIN_GLOBAL = INICIO + CFG["minutos_max"] * 60
    excluir = [x.lower() for x in CFG["excluir"]]
    db = abrir_db()
    hoy = datetime.now(CHILE).date().isoformat()
    primera_vez = db.execute("SELECT COUNT(*) FROM productos").fetchone()[0] == 0

    tiendas = [t for t in CFG.get("tiendas") or [] if t.get("activa", True)]
    for t in tiendas:
        t.setdefault("id", re.sub(r"\W+", "-", t["nombre"].lower()).strip("-"))
    rot = int(estado(db, "rotacion") or 0)
    if tiendas:
        k = rot % len(tiendas)
        tiendas = tiendas[k:] + tiendas[:k]
    estado(db, "rotacion", rot + 1)

    ofertas, codigos, resumen = [], [], []
    for i, t in enumerate(tiendas):
        if time.time() > FIN_GLOBAL - 30:
            resumen.append((t["nombre"], "-", 0, "sin tiempo en esta pasada"))
            continue
        FIN_TIENDA = time.time() + max(60, (FIN_GLOBAL - time.time()) / (len(tiendas) - i))
        tipo = t.get("tipo", "auto")
        if tipo == "auto":
            tipo = detectar(t, db, forzar=MODO == "diagnostico")
        log(f"== {t['nombre']} ({tipo})")
        n, err, vistos = 0, None, set()
        try:
            if CFG["buscar_codigos"]:
                codigos += buscar_codigos(t, db, hoy)
            for p in LECTORES[tipo](t, db):
                if not p or not p.get("sku") or not p.get("precio") or not p.get("stock"):
                    continue
                if p["precio"] < t.get("precio_minimo", CFG["precio_minimo"]):
                    continue
                nombre = (p.get("nombre") or "").lower()
                if any(x in nombre for x in excluir):
                    continue
                pid = f"{t['id']}:{p['sku']}"
                if pid in vistos:
                    continue
                vistos.add(pid)
                p["ean"] = limpiar_ean(p.get("ean"))
                p["url"] = urljoin(t["url"], p.get("url") or "")
                registrar(db, t["id"], pid, p, hoy)
                n += 1
                ev = evaluar(db, pid, p, hoy)
                if ev and not ya_avisado(db, pid, p["precio"], hoy):
                    ofertas.append({**p, **ev, "tienda": t["nombre"], "pid": pid})
                if MODO == "diagnostico" and n >= 20:
                    break
        except Exception as e:  # una tienda caída no detiene al resto
            err = f"{type(e).__name__}: {str(e)[:80]}"
            log("   ERROR", err)
        db.commit()
        if n == 0 and not err:
            err = "no se pudo leer (bloqueo o formato distinto)"
        log(f"   {n} productos")
        resumen.append((t["nombre"], tipo, n, err))

    for o in ofertas:
        o["otras"] = [x for x in otras_tiendas(db, o["pid"], o.get("ean"), hoy) if x[1] < o["precio"] * 1.5]
        db.execute("INSERT INTO avisos VALUES(?,?,?)", (o["pid"], hoy, o["precio"]))
    ofertas.sort(key=lambda o: -o["desc"])
    ofertas = ofertas[: CFG["max_ofertas_correo"]]
    limpiar_db(db, hoy)
    db.commit()
    total = db.execute("SELECT COUNT(*) FROM productos").fetchone()[0]
    log(f"Listo: {len(ofertas)} ofertas, {len(codigos)} códigos, {total} productos en historial")

    if MODO == "diagnostico":
        enviar("🔧 Ofertas Caroca: diagnóstico",
               html_correo(ofertas, codigos, resumen, f"Diagnóstico: {total} productos en historial"))
    elif ofertas or codigos:
        partes = []
        if ofertas:
            partes.append(f"{len(ofertas)} ofertas reales (hasta -{ofertas[0]['desc']*100:.0f}%)")
        if codigos:
            partes.append(f"{len(codigos)} códigos nuevos")
        enviar("⚡ Alerta de oferta - Ofertas Caroca: " + " + ".join(partes), html_correo(ofertas, codigos, [], "⚡ Alerta de oferta"))
    elif primera_vez:
        enviar("✅ Ofertas Caroca está activo",
               html_correo([], [], resumen, f"Recolectando historial: {total} productos. "
                           f"Las ofertas reales llegan desde el día {CFG['min_dias_historial']}."))
    db.close()


if __name__ == "__main__":
    main()
