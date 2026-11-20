from collections import Counter
import gzip
import json
from pathlib import Path
import shutil
from tempfile import TemporaryDirectory

from citations import citations
from proofs import IMPORT, extract_claims, mask_non_code, remove_notes


HERE = Path(__file__).resolve().parent
EXTRACTED = HERE.parent / "extracted" / "lean" / "src"
COPY = HERE / "src"
SITE = HERE / "_out" / "html-single"
PACK_SIZE = 2 * 1024 * 1024


def json_bytes(value):
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def write_pack(path, content):
    path.write_bytes(gzip.compress(content, compresslevel=6, mtime=0))


def utf16_offsets(source, claims):
    offsets = {0: 0}
    previous = 0
    positions = {position for claim in claims for position in (claim.start, claim.end, claim.statement_end)}
    for position in sorted(positions):
        offsets[position] = offsets[previous] + len(source[previous:position].encode("utf-16-le")) // 2
        previous = position
    return offsets


def pack_module(path, relative, counts):
    source, notes = remove_notes(path.read_bytes().decode("utf-8"))
    if (EXTRACTED / relative).read_bytes() != source.encode("utf-8"):
        raise ValueError(f"{relative}: the copy differs from the extracted source")
    masked = mask_non_code(source)
    claims = list(extract_claims(source, masked))
    if [claim.start for claim in claims] != [offset for offset, _, _ in notes]:
        raise ValueError(f"{relative}: expected a proof note for each declaration")
    cited_claims = [
        claim for claim, (_, status, _) in zip(claims, notes) if status == "citation"
    ]
    if cited_claims:
        written = {offset: prose for offset, status, prose in notes if status == "citation"}
        if written != dict(citations(EXTRACTED, source, masked, cited_claims)):
            raise ValueError(f"{relative}: a cited theorem no longer matches its declaration")
    positions = utf16_offsets(source, claims)
    proofs = []
    for claim, (_, status, prose) in zip(claims, notes):
        counts.update([status])
        proofs.append({
            "name": claim.name,
            "kind": claim.kind,
            "line": claim.line,
            "start": positions[claim.start],
            "statementEnd": positions[claim.statement_end],
            "end": positions[claim.end],
            "status": status,
            "prose": prose,
        })
    return json_bytes({
        "source": source,
        "imports": list(dict.fromkeys(IMPORT.findall(masked))),
        "proofs": proofs,
    })


def build():
    if not (SITE / "index.html").is_file():
        raise FileNotFoundError("Run the Verso renderer before packing the site.")
    files = {path.relative_to(COPY).as_posix(): path for path in COPY.rglob("*.lean")}
    originals = {path.relative_to(EXTRACTED).as_posix() for path in EXTRACTED.rglob("*.lean")}
    if files.keys() != originals:
        raise ValueError("The copied module paths differ from the extracted archive.")

    counts = Counter()
    catalog = []
    pack = bytearray()
    pack_number = 0
    with TemporaryDirectory(prefix="archive-", dir=SITE) as temporary:
        output = Path(temporary) / "data"
        output.mkdir()
        for index, relative in enumerate(sorted(files), 1):
            record = json_bytes(relative) + b":" + pack_module(files[relative], relative, counts)
            if pack and len(pack) + len(record) > PACK_SIZE:
                write_pack(output / f"{pack_number}.json.gz", b"{" + pack + b"}")
                pack = bytearray()
                pack_number += 1
            if pack:
                pack.extend(b",")
            pack.extend(record)
            catalog.append([relative, pack_number])
            if index % 25000 == 0:
                print(f"Packed {index:,} modules", flush=True)
        if pack:
            write_pack(output / f"{pack_number}.json.gz", b"{" + pack + b"}")
        write_pack(output / "catalog.json.gz", json_bytes({"modules": catalog, "counts": counts}))
        size = sum(path.stat().st_size for path in output.iterdir())
        if size >= 990_000_000:
            raise ValueError(f"Packed data exceeds the GitHub Pages size budget: {size:,} bytes")
        destination = SITE / "data"
        if destination.exists():
            shutil.rmtree(destination)
        output.rename(destination)

    print(f"Packed {len(catalog):,} modules and {sum(counts.values()):,} proof notes into {size:,} bytes.")
    print(" · ".join(f"{value:,} {kind}" for kind, value in sorted(counts.items())))


if __name__ == "__main__":
    build()
