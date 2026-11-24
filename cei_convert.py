#!/usr/bin/env python3
"""
Convert the filtered harvest (urkunden.jsonl, from harvest_urkunden.py) into
CEI XML files for Monasterium.net - one file per fond, containing all charters
of that fond.

The portal delivers two different record layouts, both are handled:
  * "certificate" records (ThStAM_certificate_*, saru_certificate_*):
        shelfmark, register, date, datequote, tradition, ...
  * "stat_file" records (Rudolstadt: Archivum Commune, Lehnbriefe, Documenta
    varia, ...; Meiningen: Hennebergica ...):
        unitid, unittitle.type.proper (+ .formal), unitdate, bibliography,
        provenance, GND entity links, derivate_metadata, mets_physdesc, ...

Output layout:
  <out>/<fonds>/<fonds>.cei.xml        one file per fond, multiple <cei:text> elements
  <out>/conversion_report.txt          counts, unmapped fields, physical-desc sources
  <out>/review.tsv                     records that need a human look

Mapping (CEI element <- source):
  body/idno[@id=record id]                        <- shelfmark | unitid
  chDesc/abstract                                 <- register | title (+ remark text); seal
                                                     sentences removed; witnesses appended
                                                     after " | "
  chDesc/issued/placeName + date | dateRange      <- date text / index dates; place only
                                                     when the date line starts "Ort, 1349 …"
                                                     or when a dating clause names a place
  chDesc/witnessOrig/traditioForm                 <- tradition
  chDesc/witnessOrig/archIdentifier               <- archive labels + signature + ref to
                                                     database entry
  chDesc/witnessOrig/auth/sealDesc                <- seal sentences cut from the text
  chDesc/witnessOrig/physicalDesc                 <- material and dimensions from:
                                                       - 'provenance' (legacy size field)
                                                       - derivate_metadata (physForm.*)
                                                       - mets_physdesc (MODS physicalDescription)
  chDesc/witnessOrig/note[@type=provenance]       <- residual provenance strings
  chDesc/witnessOrig/figure/graphic[@url]         <- derivate_images (IIIF manifests)
                                                     or --image-url-template
  chDesc/diplomaticAnalysis/quoteOriginaldatierung<- datequote | dating clause in the text
  chDesc/diplomaticAnalysis/listBibl*             <- bibliography (Druck / Reg. / Lit.)
  chDesc/diplomaticAnalysis/p                     <- remark lines ("Vgl. Nr. ...")
  back/persName, back/placeName [@key=gnd:...]    <- GND entity links (--no-entities to omit)

Splitting the text is conservative: only whole trailing sentences (or a trailing
"; ... siegelt" clause) that mention a seal are moved, and the witness list starts
at "Zeugen:" / "Weitere Zeugen:". Everything that is not clearly one of those stays
in the abstract; leftovers are listed in review.tsv.

Usage:
  python cei_convert.py --in harvest/urkunden.jsonl --out cei_out --xsd cei.xsd
  python cei_convert.py --selftest

Standard library only. --xsd needs `pip install xmlschema` (the CEI schema uses XSD 1.1
features that xmllint cannot handle).
"""
import argparse
import calendar
import json
import re
import sys
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict
from pathlib import Path

NS = "http://www.monasterium.net/NS/cei"
ET.register_namespace("cei", NS)

# --------------------------------------------------------------------- tables
TRADITIO = {
    "ausfertigung": "Ausfertigung",
    "beglaubigteAbschrift": "beglaubigte Abschrift",
    "nichtBeglaubigteAbschrift": "nicht beglaubigte Abschrift",
    "konzept": "Konzept",
    "duplication": "Duplikat",
    "konzeptOderKopie": "Konzept oder Kopie",
}

MONTHS = {
    "januar": 1, "jänner": 1, "jan": 1, "februar": 2, "feb": 2, "febr": 2, "märz": 3, "mär": 3,
    "april": 4, "apr": 4, "mai": 5, "juni": 6, "jun": 6, "juli": 7, "jul": 7, "august": 8,
    "aug": 8, "september": 9, "sep": 9, "sept": 9, "oktober": 10, "okt": 10, "november": 11,
    "nov": 11, "dezember": 12, "dez": 12,
}
UNDATED = {"sine", "ohne datum", "undatiert", "s.d.", "s. d.", "o. d.", "o.d."}

# input fields that are used by the converter
FIELDS_USED = {
    "id", "shelfmark", "register", "date", "datequote", "date_iso_from", "tradition",
    "derivates", "derivate_ids", "derivate_images",          # images
    "derivate_metadata", "mets_physdesc", "mets_fetched",     # physical description
    "ArchFile_class_001", "ArchFile_class_001_Label",
    "unitid", "unittitle.type.proper", "unittitle.type.formal", "unitdate", "bibliography",
    "provenance", "entitylink.gnd.href", "entitylink.gnd.title", "place.type.gnd", "place",
    "vnum", "urnLinks",
}
# fields deliberately not converted, with the reason (listed in conversion_report.txt)
FIELDS_IGNORED = {
    "quote": "citation string, rebuilt from archive labels + signature",
    "tectonics_path": "duplicate of ArchFile_class_001_Label",
    "ArchFile_class_001_Label.de": "duplicate of ArchFile_class_001_Label",
    "date_extended_search": "search-index copy of date/datequote",
    "date_iso_to": "harvester helper; precision is re-derived from the date text",
    "date_precision": "harvester helper",
    "date_uncertain": "harvester helper",
    "objectKind": "database internal", "state": "database internal",
    "file_type": "database internal (always 'certificate')",
    "propertitle": "duplicate of unittitle.type.proper",
    "indexBrowseCorporation": "search-index copy of the title",
    "unittitleSort": "sort key", "unitid.as.is": "duplicate of unitid",
    "derivate.class.derivate_types.content": "already captured inside derivate_metadata",
    "gnd": "duplicate of the entity links / place GND ids",
    "place_extended_search": "search-index copy of place",
    "entitylink.gnd.type": "database internal",
    "entitylink.gnd.significant": "duplicate of entitylink.gnd.href",
    "dateOfBirth": "biographical data of the linked GND persons, not of the charter",
    "dateOfDeath": "biographical data of the linked GND persons, not of the charter",
}

# ----------------------------------------------------------------- text helpers
SEALW = re.compile(r"(?i)\w*siegel\w*|\bsiegl\w*|\bpetschaft\w*|\bsigill\w*")
WIT = re.compile(r"(?:(?<=[.;\])])|^)\s*(?P<w>(?:Weitere\s+)?Zeug(?:e|en)\b[^:.;]{0,30}:)")
STRONG = re.compile(
    r"^(?:Es\s+siegel|Siegel\b|Siegler\b|Petschaft\b|(?:Der|Die)\s+Aussteller\w*\s+siegel"
    r"|\(\d+(?:-\d+)?\)[^.]{0,80}siegel)")
SEAL_VERB = re.compile(
    r"(?i)\bsiegel(?:t|n)\b|\b(?:mit)?besiegelung\b|\bkündig\w*\b[^.]{0,70}\bsiegel|"
    r"\b(?:hängt|hängen|drückt|drücken)\b[^.]{0,70}\bsiegel|\bbedient\w*\s+sich\b[^.]{0,40}siegel")
DATE_OPENER = re.compile(
    r"^(?:Datum\b|Dat\.|Actum\b|Gegeb\w*|Geb(?:en|enn|in)\b|Der\s+(?:ist\s+|da\s+)?geb\w*|"
    r"Die\s+geben\b|Daz\b|Geschehen\b|Am\s+tage\s+und\s+jare|A\.\s?d\.)")
GLUE = re.compile(r"(?<=[A-Za-zäöüÄÖÜß\)\]]\.)(?=[A-ZÄÖÜ\d])")
NOTE_REMARK = re.compile(
    r"^\(?(?:[Vv]gl\.|Bestätigung\b|Bestätigt\b|Auf\s+(?:der\s+)?Rückseite\b|Rückseite\b|"
    r"Dorsalvermerk\b|Rückvermerk\b)")
ABBR = {"hl", "hll", "hlg", "nr", "nrn", "st", "dr", "th", "hz", "hzg", "gf", "gfn", "kg", "ksr",
        "bzw", "vgl", "ca", "usw", "etc", "ebd", "bd", "bde", "fol", "urk", "reg", "jh", "jhs",
        "mgf", "pfgf", "lgf", "ggf", "evtl", "sog", "bes", "bf", "ebf", "ebfn", "hr", "hrn", "fr",
        "frl", "kl", "ks", "prof"}
BOUND = re.compile(r"\.\s+(?=[A-ZÄÖÜ\[(\"„])")


def norm(t):
    return re.sub(r"\s+", " ", t or "").strip()


def sentences(text):
    """Split at '. ' + capital letter, unless the word before the period is an abbreviation."""
    out, last = [], 0
    for m in BOUND.finditer(text):
        tok = re.search(r"(\S+)$", text[last:m.start()])
        tok = tok.group(1).strip("(\"„[") if tok else ""
        nxt = text[m.end():]
        if tok.endswith((")", "]")):
            ok = True
        elif "." in tok or (len(tok) == 1 and tok.isupper()) or tok.lower() in ABBR \
                or re.fullmatch(r"[A-ZÄÖÜ][a-zäöüß]{0,2}", tok):
            ok = False
            if (STRONG.match(nxt) or WIT.match(". " + nxt)) \
                    and "." not in tok and tok.lower() not in ABBR:
                ok = True
        else:
            ok = True
        if ok:
            out.append(text[last:m.start() + 1])
            last = m.end()
    out.append(text[last:])
    return [s for s in out if s]


def is_seal_sentence(s):
    if not SEALW.search(s):
        return False
    if STRONG.match(s):
        return len(s) <= 1200
    if len(s) <= 260:
        return True
    return len(s) <= 600 and bool(SEAL_VERB.search(s))


def peel_seals(text):
    """Remove trailing seal sentences (and a trailing '; ... siegelt' clause)."""
    ss = sentences(text)
    seals = []
    while len(ss) > 1 and is_seal_sentence(ss[-1]):
        seals.insert(0, ss.pop())
    last = ss[-1] if ss else ""
    if ";" in last:
        head, _, clause = last.rpartition(";")
        clause = clause.strip()
        if SEALW.search(clause) and len(clause) <= 200 and len(head) >= 40:
            ss[-1] = head.rstrip() + "."
            seals.insert(0, clause)
    return " ".join(ss), seals


def end_punct(s):
    return s if re.search(r"[.!?)\]]$", s) else s + "."


def split_glued_datequote(text, year=None):
    """stat_file titles: the dating clause is glued to the regest after a period."""
    for m in GLUE.finditer(text):
        tail = text[m.end():]
        if DATE_OPENER.match(tail) or re.match(r"\d{4}\b", tail) or (year and year in tail):
            return text[:m.start()].strip(), tail.strip()
    return text, ""


def split_tail(text, peel_dates=False):
    """-> (main, seal, witnesses, datequote) for one text."""
    text = norm(text)
    dq = []
    if peel_dates:
        ss = sentences(text)
        while len(ss) > 1 and DATE_OPENER.match(ss[-1]):
            dq.insert(0, ss.pop())
        text = " ".join(ss)
    m = WIT.search(text)
    witnesses, seals = "", []
    if m:
        before = text[:m.start("w")].strip().rstrip(";").strip()
        witseg = text[m.start("w"):].strip()
        if len(sentences(witseg)) > 1:
            witseg, seals = peel_seals(witseg)
        witnesses = witseg
    else:
        before = text
    main, s1 = peel_seals(before)
    return main, " ".join(end_punct(x) for x in s1 + seals), witnesses, " ".join(dq)


# ------------------------------------------------------------------------ dates
_MON = r"([A-Za-zäöüÄÖÜ]+)\.?"


def _month(name):
    return MONTHS.get(name.lower().rstrip("."))


def _day_ok(y, m, d):
    return m is not None and 1 <= d <= calendar.monthrange(y, m)[1]


def parse_text_date(t):
    """Parse the date text. Returns (kind, attrs, flags) or None."""
    flags = set()
    s = t.replace("[", "").replace("]", "").strip()
    if "?" in s:
        flags.add("uncertain")
        s = re.sub(r"\s*\(\?\)", "", s).replace("?", "").strip()
    s = s.rstrip(".").strip()
    if (m := re.fullmatch(r"(\d{4})", s)):
        return "date", {"value": f"{m[1]}9999"}, flags
    if (m := re.fullmatch(rf"(\d{{4}})\.? {_MON}", s)) and _month(m[2]):
        return "date", {"value": f"{m[1]}{_month(m[2]):02d}99"}, flags
    if (m := re.fullmatch(rf"(\d{{4}})\.? {_MON} (\d{{1,2}})\.?", s)):
        y, mo, d = int(m[1]), _month(m[2]), int(m[3])
        if _day_ok(y, mo, d):
            return "date", {"value": f"{y:04d}{mo:02d}{d:02d}"}, flags
    if (m := re.fullmatch(rf"(\d{{4}})\.? {_MON} (\d{{1,2}})\.?\s*[-–]\s*(\d{{1,2}})\.?", s)):
        y, mo, d1, d2 = int(m[1]), _month(m[2]), int(m[3]), int(m[4])
        if _day_ok(y, mo, d1) and _day_ok(y, mo, d2) and d1 < d2:
            return "dateRange", {"from": f"{y:04d}{mo:02d}{d1:02d}", "to": f"{y:04d}{mo:02d}{d2:02d}"}, flags
    if (m := re.fullmatch(rf"(\d{{4}})\.? {_MON}\s*[-–]\s*{_MON}", s)):
        y, m1, m2 = int(m[1]), _month(m[2]), _month(m[3])
        if m1 and m2 and m1 < m2:
            return "dateRange", {"from": f"{y:04d}{m1:02d}01",
                                 "to": f"{y:04d}{m2:02d}{calendar.monthrange(y, m2)[1]:02d}"}, flags
    if (m := re.fullmatch(r"(?:um\s+)?(\d{4})\s*[-–/]\s*(\d{4})", s)) and int(m[1]) < int(m[2]):
        if s.startswith("um"):
            flags.add("circa")
        return "dateRange", {"from": f"{m[1]}0101", "to": f"{m[2]}1231"}, flags
    if (m := re.fullmatch(r"nach (\d{4})", s)):
        return "dateRange", {"from": f"{m[1]}0101", "to": f"{m[1]}1231"}, flags | {"nach"}
    for pat in (rf"(\d{{4}}) nach {_MON} (\d{{1,2}})", rf"nach (\d{{4}}) {_MON} (\d{{1,2}})"):
        if (m := re.fullmatch(pat, s)):
            y, mo, d = int(m[1]), _month(m[2]), int(m[3])
            if _day_ok(y, mo, d):
                return "dateRange", {"from": f"{y:04d}{mo:02d}{d:02d}", "to": f"{y:04d}1231"}, flags | {"nach"}
    if (m := re.fullmatch(r"um (\d{4})", s)):
        return "date", {"value": f"{m[1]}9999"}, flags | {"circa"}
    return None


def build_date(text, f, t):
    """-> (kind, attrs, review_reason_or_None)."""
    iso = lambda x: bool(x) and re.fullmatch(r"\d{4}-\d\d-\d\d", x) is not None
    text = norm(text)
    if text.lower().rstrip(".") in {u.rstrip(".") for u in UNDATED} or text.lower() in UNDATED:
        return "date", {"value": "99999999"}, None
    parsed = parse_text_date(text)
    if parsed:
        kind, attrs, flags = parsed
        reason = None
        start = attrs.get("value") or attrs.get("from")
        if iso(f):
            fy, fm, fd = f.split("-")
            prec = 4 if start.endswith("9999") else 6 if start.endswith("99") else 8
            if start[:prec] != (fy + fm + fd)[:prec] and "nach" not in flags:
                reason = "date_text_differs_from_index"
        if reason is None and flags & {"circa", "uncertain"}:
            reason = "date_circa_or_uncertain_check"
        return kind, attrs, reason
    if not iso(f):
        return "date", {"value": "99999999"}, "undated_check_text"
    if iso(t) and t != f:
        return ("dateRange", {"from": f.replace("-", ""), "to": t.replace("-", "")},
                "date_range_from_index_check")
    return "date", {"value": f.replace("-", "")}, "date_irregular_check_value"


def strip_final_parenthetical(text):
    """'1431 Mai 27. (am suntage Cantate)' -> ('1431 Mai 27.', 'am suntage Cantate')."""
    t = text.rstrip().rstrip(".,;").rstrip()
    if not t.endswith(")"):
        return text, None
    depth = 0
    for i in range(len(t) - 1, -1, -1):
        if t[i] == ")":
            depth += 1
        elif t[i] == "(":
            depth -= 1
            if depth == 0:
                inner = t[i + 1:-1].strip()
                if not re.search(r"[A-Za-zäöüÄÖÜ]{2,}", inner):
                    return text, None
                if re.search(r"\d{4}", inner) and any(
                        w.lower().rstrip(".") in MONTHS for w in re.findall(r"[A-Za-zäöüÄÖÜ.]+", inner)):
                    return text, None
                return t[:i].rstrip(), inner
    return text, None


PLACE_PREFIX = re.compile(r"^(?P<p>[^\d]+?),\s*(?P<rest>\[?(?:nach\s+|um\s+|vor\s+)?\d{4}.*)$")


def split_place_prefix(text):
    m = PLACE_PREFIX.match(text)
    if m and len(m["p"]) <= 60:
        return m["p"].strip(), m["rest"].strip()
    return None, text


# ----------------------------------------------------------- record normalising
def first(v):
    return (v[0] if isinstance(v, list) and v else v) or ""


def parse_bibliography(entries):
    """-> list of (kind, text), kind in edition/regest/studies/plain."""
    out = []
    lab = re.compile(r"(?:(?<=\s)|^)(Drucke?|DrucK|Druck des Inserts|Reg\.|Regest|Lit\.|Literatur)\s*:\s*")
    for e in entries:
        e = norm(e)
        pos = [(m.start(), m.end(), m[1]) for m in lab.finditer(e)]
        if not pos:
            out.append(("plain", e))
            continue
        if pos[0][0] > 0 and e[:pos[0][0]].strip():
            out.append(("plain", e[:pos[0][0]].strip()))
        for i, (s, en, label) in enumerate(pos):
            seg = e[en:(pos[i + 1][0] if i + 1 < len(pos) else len(e))].strip()
            lw = label.lower()
            if lw in ("druck", "drucke"):
                out.append(("edition", seg))
            elif lw in ("reg.", "regest"):
                out.append(("regest", seg))
            elif lw in ("lit.", "literatur"):
                out.append(("studies", seg))
            else:
                out.append(("edition", f"{label}: {seg}"))
    return [(k, t) for k, t in out if t]


def normalize(rec):
    """Bring both record layouts to one structure."""
    stat = "unitid" in rec or "unittitle.type.proper" in rec
    n = {"id": rec["id"], "stat": stat, "notes": [], "remarks": []}
    n["signature"] = (rec.get("unitid") or "") if stat else "; ".join(
        s.strip() for s in (rec.get("shelfmark") or []) if s.strip())
    n["labels"] = rec.get("ArchFile_class_001_Label") or []
    n["cls"] = rec.get("ArchFile_class_001") or []
    n["derivates"] = rec.get("derivates") or rec.get("derivate_ids") or []
    n["derivate_images"] = rec.get("derivate_images") or {}
    n["derivate_metadata"] = rec.get("derivate_metadata") or {}
    n["mets_physdesc"] = rec.get("mets_physdesc") or {}
    n["mets_fetched"] = rec.get("mets_fetched")
    n["tradition"] = rec.get("tradition") or []
    n["bibliography"] = rec.get("bibliography") or []
    n["provenance"] = rec.get("provenance") or []

    if stat:
        ud = rec.get("unitdate") or [""]
        text = ud[0]
        isos = [x for x in ud[1:] if re.fullmatch(r"\d{4}-\d\d-\d\d", x)]
        n["iso_from"], n["iso_to"] = (isos[0] if isos else None), (isos[1] if len(isos) > 1 else None)
        core, paren = strip_final_parenthetical(text)
        n["issue_place"], core = split_place_prefix(core)
        n["date_text"] = core
        dq = [paren] if paren else []
        title = norm(first(rec.get("unittitle.type.proper")))
        year = (n["iso_from"] or "")[:4] or None
        title, glued = split_glued_datequote(title, year)
        if glued:
            dq.append(glued)
        main, seal, wits, dq2 = split_tail(title, peel_dates=True)
        if dq2:
            dq.append(dq2)
        seals, witnesses, mains = [seal], [wits], [main]
        formal = norm(first(rec.get("unittitle.type.formal")))
        if formal:
            if NOTE_REMARK.match(formal):
                n["remarks"].append(formal)
            else:
                fmain, fseal, fwits, _ = split_tail(formal)
                mains.append(fmain)
                seals.append(fseal)
                witnesses.append(fwits)
        n["dq"] = [norm(x) for x in dq if x]
        parts = [p for p in mains if p]
        if len(parts) == 2 and not re.search(r"[.!?:;)\]\"“”]$", parts[0]):
            parts[0] += "."
        n["main"] = " ".join(parts)
        n["seal"] = " ".join(s for s in seals if s)
        n["witnesses"] = " ".join(w for w in witnesses if w)
        vn = rec.get("vnum")
        if vn and vn != [rec.get("unitid")]:
            n["notes"].append(("vnum_differs_from_unitid", f"unitid={rec.get('unitid')} vnum={vn}"))
    else:
        n["iso_from"], n["iso_to"] = rec.get("date_iso_from"), None
        n["issue_place"] = None
        n["date_text"] = first(rec.get("date"))
        if len(rec.get("date") or []) > 1:
            n["notes"].append(("multiple_dates", " | ".join(rec["date"])))
        n["main"], n["seal"], n["witnesses"], _ = split_tail(rec.get("register", ""))
        n["dq"] = [norm(rec["datequote"])] if rec.get("datequote") else []
    n["date_text"] = norm(n["date_text"])
    if n["date_text"].endswith("."):
        n["date_text"] = n["date_text"][:-1].rstrip()

    hrefs = rec.get("entitylink.gnd.href") or []
    titles = rec.get("entitylink.gnd.title") or []
    if hrefs and len(titles) != len(hrefs):
        n["notes"].append(("gnd_person_names_misaligned", f"{len(hrefs)} ids, {len(titles)} names"))
        titles = [""] * len(hrefs)
    n["persons"] = list(zip(hrefs, titles or [""] * len(hrefs)))
    n["place_gnd"] = rec.get("place.type.gnd") or []
    n["place_names"] = [x for x in (rec.get("place") or []) if x not in n["place_gnd"]]
    n["urn"] = rec.get("urnLinks") or []
    return n


# ------------------------------------------------------- physical description
MATERIAL_RE = re.compile(
    r"(?i)\b(pergament|papier|papyrus|leinwand|seide|schafhaut|tierhaut|hadernpapier)\b")
SIZE_RE = re.compile(r"\d+(?:[.,]\d+)?\s*(?:cm|mm|m)?\s*[x×]\s*\d+(?:[.,]\d+)?", re.I)
FILE_FORMAT_RE = re.compile(r"(?i)^(?:image/(?:tiff?|jpe?g|png)|tiff?|jpe?g|png|pdf)$")


def extract_material_and_dimensions(n):
    """Collect material and dimensions from derivate_metadata and mets_physdesc.

    Returns (material_or_None, list_of_dimension_strings, list_of_source_tags).
    File-format values (image/tiff, jpeg …) are ignored — they are provenance
    for the digitised surrogate, not the charter itself.
    """
    material = None
    dims = []
    sources = []

    def add_material(v, src):
        nonlocal material
        if not material and MATERIAL_RE.search(v):
            material = v
            sources.append(src)

    def add_dim(v, src):
        if SIZE_RE.search(v) and v not in dims:
            dims.append(v)
            sources.append(src)

    # 1. Derivate Solr docs
    for der_id, dm in n.get("derivate_metadata", {}).items():
        if not isinstance(dm, dict):
            continue
        for k, v in dm.items():
            kl = k.lower()
            vals = v if isinstance(v, list) else [v]
            for x in vals:
                if not isinstance(x, str):
                    continue
                x = x.strip()
                if not x or FILE_FORMAT_RE.match(x):
                    continue
                if "material" in kl or "physform" in kl:
                    add_material(x, f"derivate:{k}")
                    if "extent" in kl or "dimension" in kl or "size" in kl:
                        add_dim(x, f"derivate:{k}")
                elif "extent" in kl or "dimension" in kl or "size" in kl:
                    add_dim(x, f"derivate:{k}")

    # 2. METS/MODS physicalDescription
    for k, v in n.get("mets_physdesc", {}).items():
        kl = k.lower()
        vals = v if isinstance(v, list) else [v]
        for x in vals:
            if not isinstance(x, str) or not x.strip():
                continue
            x = x.strip()
            if FILE_FORMAT_RE.match(x):
                continue
            if "material" in kl or kl.startswith("physdesc.form."):
                add_material(x, f"mets:{k}")
            elif "extent" in kl or "dimension" in kl:
                add_dim(x, f"mets:{k}")

    return material, dims, sources


# ------------------------------------------------------------------ XML building
def sub(parent, tag, text=None, **attrs):
    el = ET.SubElement(parent, f"{{{NS}}}{tag}", {k: v for k, v in attrs.items() if v is not None})
    if text is not None:
        el.text = text
    return el


def archive_parts(labels):
    arch = labels[0] if labels else None
    fond = " > ".join(labels[1:]) if len(labels) > 1 else None
    settlement = None
    if arch:
        m = re.search(r"(?:Haupt)?[Ss]taatsarchiv\s+([A-ZÄÖÜ][\wäöüß-]+)\s*$", arch)
        settlement = m.group(1) if m else None
    return settlement, arch, fond


DIM = re.compile(r"\d+(?:,\d+)?\s*(?:cm)?\s*x\s*\d+(?:,\d+)?\s*(?:cm)?", re.I)


def build_text_element(n, image_template=None, entities=True, db_url_template=None):
    """Build a single <cei:text> element for one charter.
    Returns (text_element, notes, info)."""
    notes = list(n["notes"])
    info = {}
    shelf = n["signature"]
    if not shelf:
        notes.append(("no_signature", ""))
        shelf = n["id"]

    text_el = ET.Element(f"{{{NS}}}text", type="charter")
    body = sub(text_el, "body")
    sub(body, "idno", shelf, id=n["id"])
    ch = sub(body, "chDesc")

    # abstract
    main, wits = n["main"], n["witnesses"]
    abstract = f"{main} | {wits}" if main and wits else (main or wits)
    if not abstract:
        notes.append(("empty_abstract", ""))
    if re.search(r"(?i)\bzeugen?\b", main):
        mm = re.search(r"(?i).{0,40}\bzeugen?\b.{0,40}", main)
        notes.append(("zeugen_word_left_in_abstract", mm.group(0)))
    mm = re.search(r".{0,50}\b\w*[Ss]iegl?\w*.{0,50}", main)
    if mm:
        notes.append(("siegel_word_left_in_abstract", mm.group(0)))
    info.update(has_seal=bool(n["seal"]), has_witnesses=bool(wits))
    sub(ch, "abstract", abstract)

    # issued
    kind, attrs, reason = build_date(n["date_text"], n["iso_from"], n["iso_to"])
    if reason:
        notes.append((reason, n["date_text"]))
    issued = sub(ch, "issued")
    if n["issue_place"]:
        key = None
        if len(n["place_gnd"]) == 1:
            core = re.sub(r"^(?:Schloss|Burg|Stadt|Kloster)\s+", "", n["issue_place"]).lower()
            if any(core == x.lower() for x in n["place_names"]):
                key = f"gnd:{n['place_gnd'][0]}"
        sub(issued, "placeName", n["issue_place"], key=key)
    sub(issued, kind, n["date_text"], **attrs)

    # witnessOrig
    wo = sub(ch, "witnessOrig")
    for tr in n["tradition"]:
        sub(wo, "traditioForm", TRADITIO.get(tr, tr))
        if tr not in TRADITIO:
            notes.append(("unknown_tradition_value", tr))
    settlement, arch, fond = archive_parts(n["labels"])
    if not arch:
        notes.append(("no_archive_label", ""))
    elif not settlement:
        notes.append(("no_settlement_derived", arch))
    ai = sub(wo, "archIdentifier")
    if settlement:
        sub(ai, "settlement", settlement)
    if arch:
        sub(ai, "arch", arch)
    if fond:
        sub(ai, "archFond", fond)
    sub(ai, "idno", shelf)
    if db_url_template:
        sub(ai, "ref", target=db_url_template.format(id=n["id"]))
    if n["seal"]:
        sub(sub(wo, "auth"), "sealDesc", n["seal"])

    # Physical description: combine provenance, derivate metadata, and METS
    prov_notes = []
    phys_material = None
    phys_dimensions = []
    phys_sources = []

    for p in n["provenance"]:
        pn = norm(p)
        if DIM.search(pn):
            mm = re.match(r"^(Pergament|Papier)\s*,\s*(.+)$", pn)
            if mm:
                phys_material = phys_material or mm[1]
                phys_dimensions.append(mm[2].strip())
            else:
                phys_dimensions.append(pn)
            phys_sources.append("provenance")
        else:
            prov_notes.append(pn)

    mat2, dims2, src2 = extract_material_and_dimensions(n)
    if mat2 and not phys_material:
        phys_material = mat2
    for d in dims2:
        if d not in phys_dimensions:
            phys_dimensions.append(d)
    phys_sources.extend(src2)

    if phys_material or phys_dimensions:
        pd = sub(wo, "physicalDesc")
        if phys_material:
            sub(pd, "material", phys_material)
        for d in phys_dimensions:
            sub(pd, "dimensions", d)
        notes.append(("physical_desc_from", "; ".join(dict.fromkeys(phys_sources))))
    info.update(has_material=bool(phys_material), has_dimensions=bool(phys_dimensions))

    for p in prov_notes:
        sub(wo, "note", p, type="provenance")

    # digitised images
    derivate_images = n.get("derivate_images") or {}
    for der in n["derivates"]:
        urls = derivate_images.get(der) or []
        if urls:
            for url in urls:
                sub(sub(wo, "figure"), "graphic", url=url)
        elif image_template:
            sub(sub(wo, "figure"), "graphic",
                url=image_template.format(derivate=der, id=n["id"]))
        else:
            suffix = " (no images in manifest)" if der in derivate_images else ""
            wo.append(ET.Comment(f" digitised images (derivate): {der}{suffix} "))

    for u in n["urn"]:
        wo.append(ET.Comment(f" persistent identifier: {u} "))

    # diplomaticAnalysis
    bibl = parse_bibliography(n["bibliography"])
    if n["dq"] or bibl or n["remarks"]:
        da = sub(ch, "diplomaticAnalysis")
        for kindname, tag in (("edition", "listBiblEdition"), ("regest", "listBiblRegest"),
                              ("studies", "listBiblErw"), ("plain", "listBibl")):
            items = [t for k, t in bibl if k == kindname]
            if items:
                lst = sub(da, tag)
                for it in items:
                    sub(lst, "bibl", it)
        if n["dq"]:
            sub(da, "quoteOriginaldatierung", " ".join(n["dq"]))
        for r in n["remarks"]:
            sub(da, "p", r)

    # back: GND entity links
    if entities and (n["persons"] or n["place_gnd"]):
        back = sub(text_el, "back")
        for gid, name in n["persons"]:
            sub(back, "persName", name or None, key=f"gnd:{gid}")
        for gid in n["place_gnd"]:
            sub(back, "placeName", key=f"gnd:{gid}")
    return text_el, notes, info


def fonds_dir(n):
    cls = n["cls"]
    name = cls[1] if len(cls) > 1 else (cls[0] if cls else "unsorted")
    return re.sub(r"[^\w.-]+", "_", name)


def write_xml(root, path):
    tree = ET.ElementTree(root)
    ET.indent(tree, space="  ")
    path.parent.mkdir(parents=True, exist_ok=True)
    tree.write(path, encoding="utf-8", xml_declaration=True)


# ------------------------------------------------------------------------ selftest
def selftest():
    sp = lambda t, **k: split_tail(t, **k)[:3]
    assert sp("Er schenkt dem Kloster Land. Siegel des Ausstellers. Zeugen: A, B und andere.") == \
        ("Er schenkt dem Kloster Land.", "Siegel des Ausstellers.", "Zeugen: A, B und andere.")
    assert sp("Die Aussteller bekunden dies [Reg. Nr. 10]. Die Aussteller siegeln (1-15).") == \
        ("Die Aussteller bekunden dies [Reg. Nr. 10].", "Die Aussteller siegeln (1-15).", "")
    assert sp("Heinrich kündigt sein Siegel an.")[1] == ""
    assert sp("Er kauft von dem Abt. Siegel des Ausstellers.")[:2] == ("Er kauft von dem Abt.", "Siegel des Ausstellers.")
    assert sp("Er kauft das Gut. Er zahlt es zu. Siegel des Ausstellers.")[:2] == \
        ("Er kauft das Gut. Er zahlt es zu.", "Siegel des Ausstellers.")
    assert sp("Er verkauft die Hufe. Zeugen: X, Y. Siegel des Ausstellers.") == \
        ("Er verkauft die Hufe.", "Siegel des Ausstellers.", "Zeugen: X, Y.")
    assert sp("Er verkauft die Hufe und gibt sie weiter; er siegelt.")[:2] == \
        ("Er verkauft die Hufe und gibt sie weiter.", "er siegelt.")
    assert sp("Er verkauft die Hufe, die zum Hof gehört. Er siegelt; Zeugen: A und B.") == \
        ("Er verkauft die Hufe, die zum Hof gehört.", "Er siegelt.", "Zeugen: A und B.")
    assert sp("Text hier. Weitere Zeugen: Dr. Johann Müller, Th. von X.")[2] == "Weitere Zeugen: Dr. Johann Müller, Th. von X."
    assert sp("Der Offizial legte eine besiegelte Urkunde vor. Er bat um eine Abschrift.")[1] == ""
    assert sp("Er verkauft. Siegel des Abts. Der Verkauf wird bestätigt.")[1] == ""
    assert sp("Er verkauft. Datum Rome a.d. 1289.", peel_dates=True)[:3] == ("Er verkauft.", "", "")
    assert split_tail("Er verkauft. Datum Rome a.d. 1289.", peel_dates=True)[3] == "Datum Rome a.d. 1289."
    assert split_glued_datequote("Er siegelt.Der gegeben ist 1436 am dornstage.") == \
        ("Er siegelt.", "Der gegeben ist 1436 am dornstage.")
    assert split_glued_datequote("Schuldig 1.000 Gulden.")[1] == ""
    assert split_glued_datequote("Er siegelt.Nikolaus war dabei.", "1436")[1] == ""

    d = lambda t, f=None, to=None: build_date(t, f, to)[:2]
    assert d("1265 August 30.", "1265-08-30") == ("date", {"value": "12650830"})
    assert d("1288", "1288-01-01") == ("date", {"value": "12889999"})
    assert d("1576 März", "1576-03-01") == ("date", {"value": "15760399"})
    assert d("1360 Mai. 25.", "1360-05-25") == ("date", {"value": "13600525"})
    assert d("1453 Jan. 20.", "1453-01-20") == ("date", {"value": "14530120"})
    assert d("[1341 Juni 11].", "1341-06-11") == ("date", {"value": "13410611"})
    assert d("[1355] August 10.", "1355-08-10") == ("date", {"value": "13550810"})
    assert d("1289 [nach Februar 22].", "1289-02-22") == ("dateRange", {"from": "12890222", "to": "12891231"})
    assert d("nach 1648 Juni 8.", "1648-06-08") == ("dateRange", {"from": "16480608", "to": "16481231"})
    assert d("[nach 1355]", "1355-01-01") == ("dateRange", {"from": "13550101", "to": "13551231"})
    assert d("[1199 - 1227]", "1199-01-01") == ("dateRange", {"from": "11990101", "to": "12271231"})
    assert d("1390 / 1395", "1390-01-01") == ("dateRange", {"from": "13900101", "to": "13951231"})
    assert d("1391 April 2-8.", "1391-04-02") == ("dateRange", {"from": "13910402", "to": "13910408"})
    assert d("1515 Mai - Juni", "1515-05-01") == ("dateRange", {"from": "15150501", "to": "15150630"})
    assert d("1827 Februar 20/21", "1827-02-20", "1827-02-21") == ("dateRange", {"from": "18270220", "to": "18270221"})
    assert d("Sine") == ("date", {"value": "99999999"})
    assert d("ohne Datum", None) == ("date", {"value": "99999999"})
    assert build_date("1452 April 25 (?).", "1452-04-25", None)[2] == "date_circa_or_uncertain_check"
    assert build_date("1265 August 31", "1265-08-30", None)[2] == "date_text_differs_from_index"
    assert build_date("vor 1348 Mai 22.", "1348-05-21", None)[2] == "date_irregular_check_value"
    assert build_date("1453 Jan. 20. oder 21.", "1453-01-20", None)[2] == "date_irregular_check_value"
    assert strip_final_parenthetical("1431 Mai 27. (am suntage Cantate)") == ("1431 Mai 27.", "am suntage Cantate")
    assert strip_final_parenthetical("1452 April 25 (?).")[1] is None
    assert strip_final_parenthetical("1641 Sep. 29. (1669 Sep. 28)")[1] is None
    assert