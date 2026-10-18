#!/usr/bin/env python3
"""
Harvest Urkunden metadata from the Landesarchiv Thüringen portal
(staatsarchive.thulb.uni-jena.de, MyCoRe/Solr) as a basis for CEI XML
(Monasterium.net).

Output (in --out, default ./harvest):
  raw/page_<start>.json        untouched Solr responses (resume + audit trail)
  raw/manifests/<derivate>.json untouched IIIF manifests (--with-manifests only)
  urkunden_raw.jsonl           every document with ALL fields, one per line
  urkunden.jsonl               filtered: internal/duplicate fields removed,
                               derived fields added (see derive())
  fields_report.txt            every field name seen, with count -> use this to
                               spot fields the filter should keep or drop

Usage:
  python harvest_urkunden.py                          # live harvest, all archives
  python harvest_urkunden.py --with-manifests         # + one IIIF manifest per derivate
  python harvest_urkunden.py --delay 2                # slower
  python harvest_urkunden.py --from-file urkunden.json   # offline test on a saved response

Notes:
  * Requires only the standard library.
  * If the server answers with a bot challenge (HTML instead of JSON), the
    script stops. It does NOT try to get around it - ask the archive/ThULB.
  * --with-manifests adds one HTTP request per unique derivate. Manifests are
    cached in raw/manifests/, so re-runs cost nothing. Use --delay to be
    gentle to the server.
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
from collections import Counter
from pathlib import Path

BASE = "https://staatsarchive.thulb.uni-jena.de/servlets/solr/stat2_restricted"
MANIFEST_URL = (
    "https://staatsarchive.thulb.uni-jena.de/api/iiif/presentation/v2/{derivate}/manifest"
)
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
}
DROP_PATTERNS = [
    re.compile(r"^search_result_link_text"),
    re.compile(r"^sortBy\."),
    re.compile(r"^ArchFile_class_001\.id\.in\.position\."),
]
ISO = re.compile(r"^\d{4}-\d{2}-\d{2}$")


def keep_field(name):
    return name not in DROP_EXACT and not any(p.search(name) for p in DROP_PATTERNS)


def filter_doc(doc):
    out = {k: v for k, v in doc.items() if keep_field(k)}
    # drop language variants that are identical to the base field
    for k in list(out):
        m = re.match(r"^(.*)\.(de|en)$", k)
        if m and m.group(1) in out and out[m.group(1)] == out[k]:
            del out[k]
    # *_Label.de duplicating *_Label (pattern above does not match "_Label.de")
    if out.get("ArchFile_class_001_Label.de") == out.get("ArchFile_class_001_Label"):
        out.pop("ArchFile_class_001_Label.de", None)
    return out


def derive(doc, out):
    """Add helper fields that make the CEI conversion easier."""
    des = doc.get("date_extended_search") or []
    isos = [d for d in des if ISO.match(d)]
    if isos:
        # the index stores from/to (identical for single-day dates) up front
        out["date_iso_from"] = isos[0]
        out["date_iso_to"] = isos[1] if len(isos) > 1 else isos[0]
    # date written in the source vs. editorial supplement in brackets
    date = (doc.get("date") or [""])[0]
    out["date_uncertain"] = "[" in date or "?" in date
    # The index stores year-only / month-only dates as the FIRST day of the
    # period for both ends. Widen the end of the range so it fits CEI dateRange.
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
    # shelfmark of the whole fonds path as one readable string
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
            if "rep-pow-challenge" in final or body.lstrip().startswith("<"):
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
    """Fetch (and cache) the IIIF Presentation 2.1 manifest for one derivate.
    Returns the parsed JSON, or None if it cannot be fetched."""
    cache = raw_dir / "manifests" / f"{derivate}.json"
    if cache.exists():
        try:
            return json.loads(cache.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            cache.unlink()  # corrupt cache, refetch
    url = MANIFEST_URL.format(derivate=urllib.parse.quote(derivate, safe=""))
    for attempt in range(1, retries + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=60) as r:
                body = r.read().decode("utf-8")
            if body.lstrip().startswith("<"):
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
    """Turn a manifest identifier / image-service endpoint into a served image URL."""
    # 1. Image-service endpoint: append the IIIF Image API parameters.
    if svc:
        if "/full/" in svc or svc.rstrip("/").endswith("default.jpg"):
            return svc                      # already a full Image API URL
        return svc.rstrip("/") + IMAGE_SUFFIX
    if not rid:
        return None
    # 2. Raw @id that already contains the Image API parameters.
    if "/full/" in rid:
        return rid
    # 3. Bare identifier (the .tif case): append the parameters ourselves.
    return rid.rstrip("/") + IMAGE_SUFFIX


def manifest_images(manifest):
    """Served image URLs, in canvas order (Presentation 2.1 and 3.0)."""
    if not manifest:
        return []
    urls = []
    # Presentation 2.1
    for seq in manifest.get("sequences", []):
        for canvas in seq.get("canvases", []):
            for img in canvas.get("images", []):
                res = img.get("resource") or {}
                urls.append(_served_url(_resource_id(res), _service_id(res)))
    # Presentation 3.0 (harmless no-op for 2.1 manifests)
    for canvas in manifest.get("items", []):
        for page in canvas.get("items", []):
            for ann in page.get("items", []):
                body = ann.get("body") or {}
                if isinstance(body, list):
                    body = body[0] if body else {}
                urls.append(_served_url(_resource_id(body), _service_id(body)))
    return [u for u in urls if u]


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
    args = ap.parse_args()

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
            if page_file.exists():  # resume
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

    # de-duplicate by id (paging over a changing index can repeat records)
    seen, unique = set(), []
    for d in docs:
        if d["id"] not in seen:
            seen.add(d["id"])
            unique.append(d)
    if len(unique) != len(docs):
        print(f"Removed {len(docs) - len(unique)} duplicate records", file=sys.stderr)

    # ---------------------------------------------------------------- manifests
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
            ff.write(json.dumps(out, ensure_ascii=False) + "\n")

    with open(out_dir / "fields_report.txt", "w", encoding="utf-8") as f:
        for name, n in sorted(field_counts.items()):
            f.write(f"{n:7d}  {'KEEP' if keep_field(name) else 'drop'}  {name}\n")

    print(f"Wrote {len(unique)} records to {out_dir}/ (see fields_report.txt)")


if __name__ == "__main__":
    main()