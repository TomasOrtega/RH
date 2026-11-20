import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
import json
from pathlib import Path

from citations import citations
from proofs import explain, extract_claims, insert_notes, mask_non_code, remove_notes


HERE = Path(__file__).resolve().parent
EXTRACTED = HERE.parent / "extracted" / "lean" / "src"
COPY = HERE / "src"
AUTHORED = json.loads((HERE / "authored.json").read_text(encoding="utf-8"))


def annotate_module(relative):
    original = (EXTRACTED / relative).read_bytes()
    source = original.decode("utf-8")
    masked = mask_non_code(source)
    claims = list(extract_claims(source, masked))
    authored = AUTHORED.get(relative, {})
    written = {}
    used = set()
    if authored:
        for claim in claims:
            location = f"{claim.name}:{claim.line}"
            key = location if location in authored else claim.name
            if key in authored:
                written[claim.start] = authored[key]
                used.add(key)
    absent = authored.keys() - used
    if absent:
        raise ValueError(f"{relative}: authored explanations have no declaration: {sorted(absent)}")
    cited = dict(citations(EXTRACTED, source, masked, (claim for claim in claims if claim.start not in written)))
    notes = []
    for claim in claims:
        if claim.start in written:
            notes.append(("authored", written[claim.start]))
        elif claim.start in cited:
            notes.append(("citation", cited[claim.start]))
        else:
            notes.append(explain(source, masked, claim))
    annotated = insert_notes(source, claims, notes)
    stripped, stored = remove_notes(annotated)
    if stripped != source or [offset for offset, _, _ in stored] != [claim.start for claim in claims]:
        raise ValueError(f"{relative}: failed to preserve the declaration source")
    target = COPY / relative
    content = annotated.encode("utf-8") if notes else original
    if not target.is_file() or target.read_bytes() != content:
        target.parent.mkdir(parents=True, exist_ok=True)
        temporary = target.with_suffix(".lean.tmp")
        temporary.write_bytes(content)
        temporary.replace(target)
    counts = Counter(status for status, _ in notes)
    counts["modules"] = 1
    return counts


def report(results):
    counts = Counter()
    for result in results:
        counts.update(result)
        if counts["modules"] % 25000 == 0:
            print(f"{counts['modules']:,} modules", flush=True)
    return counts


def main():
    parser = argparse.ArgumentParser(description="Add source-derived English proof notes to the copied Lean files.")
    parser.add_argument("modules", nargs="*", help="Paths relative to the extracted src")
    parser.add_argument("--jobs", type=int, default=6)
    args = parser.parse_args()
    paths = args.modules or sorted(file.relative_to(EXTRACTED).as_posix() for file in EXTRACTED.rglob("*.lean"))
    for relative in paths if args.modules else ():
        if relative.startswith("/") or ".." in Path(relative).parts or not relative.endswith(".lean"):
            parser.error(f"Expected a relative .lean path, got {relative}")
    if args.jobs == 1:
        counts = report(map(annotate_module, paths))
    else:
        with ProcessPoolExecutor(max_workers=args.jobs) as pool:
            counts = report(pool.map(annotate_module, paths, chunksize=48))
    print(" · ".join(f"{value:,} {kind}" for kind, value in sorted(counts.items())), flush=True)


if __name__ == "__main__":
    main()
