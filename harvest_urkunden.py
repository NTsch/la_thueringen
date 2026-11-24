#!/usr/bin/env python3
"""
Harvest Urkunden metadata from the Landesarchiv Thüringen portal
(staatsarchive.thulb.uni-jena.de, MyCoRe/Solr) as a basis for CEI XML
(Monasterium.net).

Output (in --out, default ./harvest):
  raw/page_<start>.json           untouched Solr responses (resume + audit trail)
  raw/manifests/<derivate>.json   untouched IIIF manifests (--with-manifests only)
  raw/derivates/<derivate>.json   derivate Solr docs (--with-derivates only)
  raw/mets/<record>.xml           METS/MODS full exports (--with-mets only)
  urkunden_raw.jsonl              every document with ALL fields, one per line
  urkunden.jsonl                  filtered: internal/duplicate fields removed,
                                  derived fields added (see derive()), and — if
                                  requested — derivate_metadata / mets_physdesc.
  fields_report.txt               every field name seen, with count

Usage:
  python harvest_urkunden.py                          # live harvest, all archives
  python harvest_urkunden.py --enrich                 # + manifests + derivates + METS
  python harvest_urkunden.py --with-derivates         # only derivate Solr docs
  python harvest_urkunden.py --from-file urkunden.json

Notes:
  * Requires only the standard library.
  * --enrich adds up to three HTTP requests per record:
      - one IIIF presentation manifest per derivate
      - one Solr doc per derivate
      - one METS export per base object
    All are cached; re-runs cost nothing beyond reading the cache.
    First full --enrich harvest of ~700 records at --delay 1.5 ≈ 45 min.
  * If the server answers with a bot challenge / HTML, the script stops for the
    primary Solr query and skips the affected derivate/METS, but keeps going.
"""
import argparse
import calendar
import json
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict
from pathlib import Path

BASE = "https://staatsarchive.thulb.uni-jena.de/servlets/solr/stat2_restricted"
MANIFEST_URL = (
    "https://staatsarchive.thulb.uni-jena.de/api/iiif/presentation/v2/{derivate}/manifest"
)
METS_URL = "https://staatsarchive.thulb.uni-jena.de/receive/{id}?XSL.Transformer=METS"
USER_AGENT = "urkunden-harvest/1.0 (research; contact: niklas.tscherne@uni-graz.at)"

# Fields dropped from the filtered output: database-internal or duplicates.
DROP_EXACT = {
    # database bookkeeping
    "returnId", "objectProject", "objectType", "link", "created", "modified",
    "createdby", "modifiedby", "derCount", "worldReadable",
    "worldReadableComplete", "_version_", "facetObjectType",
    # alternative/raw shelfmark forms and sort keys (shelfmark itself is kept)
    "shelfmark.as.is", "shelfmark.type.actual.raw", "shelfmark.sort",
    # duplicates of register / date
    "title", "facets.date.published", "category", "category.top",
    "component", "component.top",
    # tectonics helper fields (ArchFile_class_001 + labels are kept)
    "ArchFile_class_001.leaf", "ArchFile_class_001.root",
    # link to the holding archive itself, same for every record
    "entitylink.type", "entitylinktext.corporation",
    # derivate field duplicated into the parent doc; full data now lives in
    # derivate_metadata via --with-derivates
    "derivate.class.derivate_types.content",
}
DROP_PATTERNS = [
    re.compile(r"^search_result_link_text"),
    re.compile(r"^sortBy\."),
    re.compile(r"^ArchFile_class_001\.id\.in\.position\."),
]
ISO = re.compile(r"^\d{4}-\d{2}-\d{2}$")
HTML_START = re.compile(r"^\s*<(!doctype|html)", re.I)


def keep_field(name):
    return name not in DROP_EXACT and not any(p.search(name) for p in DROP_PATTERNS)


def filter_doc(doc):
    out = {k: v for k, v in doc.items() if keep_field(k)}
    # drop language variants that are identical to the base field
    for k in list(out):
        m = re.match(r"^(.*)\.(de|en)$", k)
        if m and m.group(1) in out and out[m.group(1)] == out[k]:
            del out[k]
    # *_Label.de duplicating *_Label
    if out.get("ArchFile_class_001_Label.de") == out.get("ArchFile_class_001_Label"):
        out.pop("ArchFile_class_001_Label.de", None)
    return out


def derive(doc, out):
    """Add helper fields that make the CEI conversion easier."""
    des = doc.get("date_extended_search") or []
    isos = [d for d in des if ISO.match(d)]
    if isos:
        out["date_iso_from"] = isos[0]
        out["date_iso_to"] = isos[1] if len(isos) > 1 else isos[0]
    date = (doc.get("date") or [""])[0]
    out["date_uncertain"] = "[" in date or "?" in date
    if "date_iso_from" in out:
        y, m, _d = (int(x) for x in out["date_iso_from"].split("-"))
        bare = date.strip(" .")
        if re.fullmatch(r"\d{4}", bare):
            out["date_precision"] = "year"
            out["date_iso_to"] = f"{y:04d}-12-31"
        elif re.fullmatch(r"\d{4} [^\d\W]+", bare):
            out["date_precision"] = "month"
            out["date_iso_to"] = f"{y:04d}-{m:02d}-{calendar.monthrange(y, m)[1]:02d}"
        elif out["date_uncertain"]:
            out["date_precision"] = "approximate"
        else:
            out["date_precision"] = "day"
    labels = doc.get("ArchFile_class_001_Label") or []
    if labels:
        out["tectonics_path"] = " > ".join(labels)
    out["derivate_ids"] = doc.get("derivates", [])
    return out


def process(doc):
    return derive(doc, filter_doc(doc))


def fetch(start, rows, query, sort, retries=4):
    params = {
        "qry": query,
        "fq": 'facetObjectType:("Urkunde")',
        "wt": "json",
        "rows": rows,
        "start": start,
        "sort": sort,
    }
    url = BASE + "?" + urllib.parse.urlencode(params)
    for attempt in range(1, retries + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=60) as r:
                body = r.read().decode("utf-8")
                final = r.geturl()
            if "rep-pow-challenge" in final or HTML_START.match(body):
                sys.exit(
                    "Server returned a bot challenge / HTML instead of JSON.\n"
                    f"URL: {final}\nStopping. Please contact the archive or ThULB "
                    "about permitted bulk access."
                )
            return json.loads(body)
        except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as e:
            wait = 5 * attempt
            print(f"  attempt {attempt} failed ({e}); retrying in {wait}s", file=sys.stderr)
            time.sleep(wait)
    sys.exit(f"Giving up at start={start}")


# --------------------------------------------------------------- IIIF manifests

def fetch_manifest(derivate, raw_dir, delay, retries=1):
    """Fetch (and cache) the IIIF Presentation 2.1 manifest for one derivate."""
    cache = raw_dir / "manifests" / f"{derivate}.json"
    if cache.exists():
        try:
            return json.loads(cache.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            cache.unlink()
    url = MANIFEST_URL.format(derivate=urllib.parse.quote(derivate, safe=""))
    for attempt in range(1, retries + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=60) as r:
                body = r.read().decode("utf-8")
            if HTML_START.match(body):
                print(f"  manifest {derivate}: HTML answer (challenge?), skipping",
                      file=sys.stderr)
                return None
            data = json.loads(body)
            cache.parent.mkdir(parents=True, exist_ok=True)
            cache.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
            time.sleep(delay)
            return data
        except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as e:
            wait = 5 * attempt
            print(f"  manifest {derivate} attempt {attempt} failed ({e}); retrying in {wait}s",
                  file=sys.stderr)
            time.sleep(wait)
    print(f"  giving up on manifest {derivate}", file=sys.stderr)
    return None


IMAGE_SUFFIX = "/full/full/0/default.jpg"


def _resource_id(res):
    return res.get("@id") or res.get("id")


def _service_id(res):
    svc = res.get("service")
    if isinstance(svc, list):
        svc = svc[0] if svc else None
    if isinstance(svc, dict):
        return svc.get("@id") or svc.get("id")
    return svc if isinstance(svc, str) else None


def _served_url(rid, svc):
    if svc:
        if "/full/" in svc or svc.rstrip("/").endswith("default.jpg"):
            return svc
        return svc.rstrip("/") + IMAGE_SUFFIX
    if not rid:
        return None
    if "/full/" in rid:
        return rid
    return rid.rstrip("/") + IMAGE_SUFFIX


def manifest_images(manifest):
    """Served image URLs, in canvas order (Presentation 2.1 and 3.0)."""
    if not manifest:
        return []
    urls = []
    for seq in manifest.get("sequences", []):
        for canvas in seq.get("canvases", []):
            for img in canvas.get("images", []):
                res = img.get("resource") or {}
                urls.append(_served_url(_resource_id(res), _service_id(res)))
    for canvas in manifest.get("items", []):
        for page in canvas.get("items", []):
            for ann in page.get("items", []):
                body = ann.get("body") or {}
                if isinstance(body, list):
                    body = body[0] if body else {}
                urls.append(_served_url(_resource_id(body), _service_id(body)))
    return [u for u in urls if u]


# ---------------------------------------------------------- derivate Solr docs

def fetch_derivate_doc(der_id, raw_dir, delay, retries=2):
    """Fetch and cache the full Solr doc for one derivate.

    Returns the derivate dict, an empty dict if the derivate is not in Solr, or
    None on a network failure (so the caller can distinguish). Empty results
    are cached as `{}` so we do not refetch known-missing derivates.
    """
    cache = raw_dir / "derivates" / f"{der_id}.json"
    if cache.exists():
        try:
            return json.loads(cache.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            cache.unlink()

    params = {
        "qry": f"id:{der_id}",
        "wt": "json",
        "fl": "*",
        "rows": 1,
    }
    url = BASE + "?" + urllib.parse.urlencode(params)
    for attempt in range(1, retries + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=60) as r:
                body = r.read().decode("utf-8")
            if HTML_START.match(body):
                print(f"  derivate {der_id}: HTML/challenge, skipping", file=sys.stderr)
                return None
            data = json.loads(body)
            docs = data.get("response", {}).get("docs", [])
            doc = docs[0] if docs else {}
            cache.parent.mkdir(parents=True, exist_ok=True)
            cache.write_text(json.dumps(doc, ensure_ascii=False), encoding="utf-8")
            time.sleep(delay)
            return doc
        except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as e:
            wait = 5 * attempt
            print(f"  derivate {der_id} attempt {attempt} failed ({e}); retrying in {wait}s",
                  file=sys.stderr)
            time.sleep(wait)
    print(f"  giving up on derivate {der_id}", file=sys.stderr)
    return None


def extract_derivate_fields(doc):
    """Keep derivate-relevant fields from a derivate Solr doc.

    We keep every field that is not obvious bookkeeping so that a future
    schema change (a new `derivate.class.…` field) is captured automatically
    instead of silently being missed again.
    """
    if not doc:
        return {}
    DROP = {"_version_", "score", "worldReadable", "worldReadableComplete",
            "created", "modified", "createdby", "modifiedby",
            "returnId", "objectProject", "objectType",
            "derivate.class.derivate_types.content"}  # internal derivate id
    return {k: v for k, v in doc.items() if k not in DROP}


# ---------------------------------------------------------------------- METS

def fetch_mets(rec_id, raw_dir, delay, retries=2):
    """Fetch (and cache) the METS/MODS export for one Urkunde record.

    Returns the XML text, or None if the export could not be fetched or did
    not look like a METS document. Successful XML is cached raw so we can
    re-parse it later without re-hitting the server.
    """
    cache = raw_dir / "mets" / f"{rec_id}.xml"
    if cache.exists():
        return cache.read_text(encoding="utf-8")
    url = METS_URL.format(id=urllib.parse.quote(rec_id, safe=""))
    for attempt in range(1, retries + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=60) as r:
                body = r.read().decode("utf-8")
            if HTML_START.match(body) or "<mets" not in body:
                print(f"  mets {rec_id}: not a METS response, skipping", file=sys.stderr)
                return None
            try:
                ET.fromstring(body)
            except ET.ParseError as e:
                print(f"  mets {rec_id}: XML parse error ({e}), skipping", file=sys.stderr)
                return None
            cache.parent.mkdir(parents=True, exist_ok=True)
            cache.write_text(body, encoding="utf-8")
            time.sleep(delay)
            return body
        except (urllib.error.URLError, TimeoutError) as e:
            wait = 5 * attempt
            print(f"  mets {rec_id} attempt {attempt} failed ({e}); retrying in {wait}s",
                  file=sys.stderr)
            time.sleep(wait)
    print(f"  giving up on METS for {rec_id}", file=sys.stderr)
    return None


def _localname(tag):
    return tag.split("}", 1)[1] if "}" in tag else tag


def extract_mets_info(mets_xml):
    """Pull physicalDescription and file-format info out of a METS/MODS XML.

    Values are aggregated under `physdesc.<tag>.<type>` and `file.format`.
    Everything else stays in the raw cache for future re-parsing.
    """
    if not mets_xml:
        return {}
    try:
        root = ET.fromstring(mets_xml)
    except ET.ParseError:
        return {}

    out = defaultdict(list)

    # MODS physicalDescription (material, extent, dimensions, note, …)
    for el in root.iter():
        if _localname(el.tag) != "physicalDescription":
            continue
        for child in el:
            typ = child.get("type", "value")
            val = (child.text or "").strip()
            if val:
                out[f"physdesc.{_localname(child.tag)}.{typ}"].append(val)

    # METS file-group entries carry the served file MIME type / format
    for el in root.iter():
        if _localname(el.tag) == "file":
            fmt = el.get("MIMETYPE") or el.get("FORMAT")
            if fmt:
                out["file.format"].append(fmt)

    return {k: sorted(set(v)) for k, v in out.items()}


# ------------------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="harvest")
    ap.add_argument("--rows", type=int, default=100)
    ap.add_argument("--delay", type=float, default=1.5, help="seconds between requests")
    ap.add_argument("--query", default="*:*", help="value for the qry parameter")
    ap.add_argument("--sort", default="id asc")
    ap.add_argument("--from-file", help="process a saved Solr JSON response instead of fetching")
    ap.add_argument("--with-manifests", action="store_true",
                    help="fetch IIIF manifests for every derivate and store the "
                         "resulting image URLs as 'derivate_images'")
    ap.add_argument("--with-derivates", action="store_true",
                    help="fetch full Solr docs for every derivate; store useful "
                         "fields under 'derivate_metadata'")
    ap.add_argument("--with-mets", action="store_true",
                    help="fetch the METS/MODS export for every record; store "
                         "physicalDescription and file formats under 'mets_physdesc'")
    ap.add_argument("--enrich", action="store_true",
                    help="shortcut for --with-manifests --with-derivates --with-mets")
    args = ap.parse_args()

    if args.enrich:
        args.with_manifests = True
        args.with_derivates = True
        args.with_mets = True

    out_dir = Path(args.out)
    raw_dir = out_dir / "raw"
    raw_dir.mkdir(parents=True, exist_ok=True)

    docs = []
    if args.from_file:
        data = json.loads(Path(args.from_file).read_text(encoding="utf-8"))
        docs = data["response"]["docs"]
        print(f"Loaded {len(docs)} docs from {args.from_file} "
              f"(numFound={data['response']['numFound']})")
    else:
        start, total = 0, None
        while total is None or start < total:
            page_file = raw_dir / f"page_{start:07d}.json"
            if page_file.exists():
                data = json.loads(page_file.read_text(encoding="utf-8"))
            else:
                data = fetch(start, args.rows, args.query, args.sort)
                page_file.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
                time.sleep(args.delay)
            total = data["response"]["numFound"]
            page_docs = data["response"]["docs"]
            if not page_docs:
                break
            docs.extend(page_docs)
            start += len(page_docs)
            print(f"{min(start, total)}/{total}")

    seen, unique = set(), []
    for d in docs:
        if d["id"] not in seen:
            seen.add(d["id"])
            unique.append(d)
    if len(unique) != len(docs):
        print(f"Removed {len(docs) - len(unique)} duplicate records", file=sys.stderr)

    # ------------------------------------------------------------ manifests
    der_images = {}
    if args.with_manifests:
        derivates = sorted({der for d in unique for der in (d.get("derivates") or [])})
        print(f"Fetching IIIF manifests for {len(derivates)} derivates ...")
        ok = 0
        for i, der in enumerate(derivates, 1):
            m = fetch_manifest(der, raw_dir, args.delay)
            imgs = manifest_images(m)
            der_images[der] = imgs
            if imgs:
                ok += 1
            if i % 25 == 0 or i == len(derivates):
                print(f"  manifests: {i}/{len(derivates)} (with images: {ok})")

    # ------------------------------------------------------------ derivates
    der_meta_by_id = {}
    if args.with_derivates:
        all_ders = sorted({der for d in unique for der in (d.get("derivates") or [])})
        print(f"Fetching derivate Solr docs for {len(all_ders)} derivates ...")
        ok = 0
        der_fields = Counter()
        for i, der in enumerate(all_ders, 1):
            meta = fetch_derivate_doc(der, raw_dir, args.delay)
            # distinguish "not in Solr" ({}) from "network failure" (None)
            der_meta_by_id[der] = extract_derivate_fields(meta or {})
            if meta:
                ok += 1
                for k in meta:
                    der_fields[k] += 1
            if i % 25 == 0 or i == len(all_ders):
                print(f"  derivates: {i}/{len(all_ders)} (ok: {ok})")
        if ok == 0:
            print("  WARNING: derivate Solr docs not found for any derivate; "
                  "--with-derivates added no data. Check the Solr schema or use "
                  "--with-mets instead.", file=sys.stderr)
        else:
            print(f"  derivate fields seen: {len(der_fields)} unique — "
                  f"top: {[k for k, _ in der_fields.most_common(5)]}")

    # ------------------------------------------------------------ METS
    mets_by_id = {}
    if args.with_mets:
        print(f"Fetching METS exports for {len(unique)} records ...")
        ok = 0
        mets_fields = Counter()
        for i, d in enumerate(unique, 1):
            xml = fetch_mets(d["id"], raw_dir, args.delay)
            if xml:
                info = extract_mets_info(xml)
                mets_by_id[d["id"]] = info
                for k in info:
                    mets_fields[k] += 1
                ok += 1
            if i % 25 == 0 or i == len(unique):
                print(f"  METS: {i}/{len(unique)} (ok: {ok})")
        if ok == 0:
            print("  WARNING: no METS exports could be fetched; "
                  "--with-mets added no data.", file=sys.stderr)
        else:
            print(f"  METS physicalDescription fields seen: "
                  f"{sorted(mets_fields)[:8]}")

    # ------------------------------------------------------------ output
    field_counts = Counter(k for d in unique for k in d)
    with open(out_dir / "urkunden_raw.jsonl", "w", encoding="utf-8") as fr, \
         open(out_dir / "urkunden.jsonl", "w", encoding="utf-8") as ff:
        for d in unique:
            fr.write(json.dumps(d, ensure_ascii=False) + "\n")
            out = process(d)
            if args.with_manifests:
                out["derivate_images"] = {
                    der: der_images.get(der, []) for der in (d.get("derivates") or [])
                }
            if args.with_derivates:
                out["derivate_metadata"] = {
                    der: der_meta_by_id.get(der, {})
                    for der in (d.get("derivates") or [])
                }
            if args.with_mets:
                out["mets_fetched"] = d["id"] in mets_by_id
                out["mets_physdesc"] = mets_by_id.get(d["id"], {})
            ff.write(json.dumps(out, ensure_ascii=False) + "\n")

    with open(out_dir / "fields_report.txt", "w", encoding="utf-8") as f:
        for name, n in sorted(field_counts.items()):
            f.write(f"{n:7d}  {'KEEP' if keep_field(name) else 'drop'}  {name}\n")

    print(f"Wrote {len(unique)} records to {out_dir}/ (see fields_report.txt)")


if __name__ == "__main__":
    main()