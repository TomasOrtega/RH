"""Write a proof by reference for wrappers of an imported theorem."""

from functools import lru_cache
from pathlib import Path
import re
from urllib.parse import urlencode

from proofs import COMMAND, DECLARATION_NAME, IMPORT, PLACEHOLDER, code, compact, extract_claims, mask_non_code


IDENTIFIER = r"[^\W\d][\w'’]*"
NAME = rf"{IDENTIFIER}(?:\.{IDENTIFIER})*"
QUALIFIED = rf"{IDENTIFIER}(?:\.{IDENTIFIER})+"
SCOPE = re.compile(
    r"^[ \t]*(?:(?:noncomputable|public|private)[ \t]+)*"
    r"(namespace|section|mutual|end)\b([^\n]*)",
    re.MULTILINE,
)
WRAPPER = re.compile(
    rf"by first \| exact @(?P<name>{QUALIFIED}) \| exact (?P=name)"
    r"(?: \| \(intros; apply (?P=name)(?: <;> assumption|; all_goals assumption)\))?"
)
DIRECT = re.compile(rf"(?:by exact )?@?(?P<name>_root_\.{QUALIFIED})")
PRIVATE = re.compile(r"\bprivate\s+(?:theorem|lemma)\b")
QUOTED = re.compile(r'["«\x60]')


def signature(source, masked, claim):
    command = COMMAND.match(masked, claim.start)
    name = DECLARATION_NAME.match(source, command.end())
    if name is None or QUOTED.search(source, name.end(), claim.statement_end):
        return None
    return compact(masked[name.end():claim.statement_end]) or None


def apply_scope(scopes, event):
    action, rest = event.groups()
    name = rest.strip()
    if name and not re.fullmatch(NAME, name):
        return False
    if action == "end":
        if not scopes:
            return False
        previous, _ = scopes.pop()
        return not name or name in {previous, previous.rsplit(".", 1)[-1]}
    if action == "namespace" and (not name or name.startswith("_root_.")):
        return False
    scopes.append((name, name if action == "namespace" else ""))
    return True


@lru_cache(maxsize=2048)
def exported_claims(path):
    try:
        source = path.read_bytes().decode("utf-8")
    except FileNotFoundError:
        return {}
    masked = mask_non_code(source)
    events = iter(SCOPE.finditer(masked))
    next_event = next(events, None)
    scopes = []
    names = {}
    for claim in extract_claims(source, masked):
        while next_event and next_event.start() < claim.start:
            if not apply_scope(scopes, next_event):
                return {}
            next_event = next(events, None)
        if claim.kind not in {"lemma", "theorem"} or claim.proof_start is None:
            continue
        if PRIVATE.search(masked, claim.start, claim.statement_end) or PLACEHOLDER.search(masked, claim.proof_start, claim.end):
            continue
        if not re.fullmatch(NAME, claim.name):
            continue
        if claim.name.startswith("_root_."):
            qualified = claim.name.removeprefix("_root_.")
        else:
            qualified = ".".join([part for _, part in scopes if part] + [claim.name])
        statement = signature(source, masked, claim)
        if statement:
            names.setdefault(qualified, []).append((statement, claim.line))
    if next_event and not apply_scope(scopes, next_event):
        return {}
    for event in events:
        if not apply_scope(scopes, event):
            return {}
    return names if all(not label for label, _ in scopes) else {}


def citations(root, source, masked, claims):
    imports = {
        Path(*module.split(".")).with_suffix(".lean")
        for module in IMPORT.findall(masked)
        if re.fullmatch(NAME, module)
    }
    for claim in claims:
        if claim.kind not in {"lemma", "theorem"} or claim.proof_start is None:
            continue
        if QUOTED.search(source, claim.proof_start, claim.end):
            continue
        body = compact(masked[claim.proof_start:claim.end])
        match = WRAPPER.fullmatch(body) or DIRECT.fullmatch(body)
        if match is None:
            continue
        name = match["name"].removeprefix("_root_.")
        statement = signature(source, masked, claim)
        if statement is None:
            continue
        targets = [
            (module, other_statement, line)
            for module in imports
            for other_statement, line in exported_claims(root / module).get(name, ())
        ]
        if len(targets) != 1:
            continue
        module, other_statement, line = targets[0]
        if statement == other_statement:
            query = urlencode({"module": module.as_posix(), "line": line})
            prose = (
                f"Apply {code(name)} to the given parameters and hypotheses. "
                "The imported theorem has the same written statement and gives the conclusion directly."
                f"\n\n[Source theorem](?{query}#L{line})"
            )
            yield claim.start, prose
