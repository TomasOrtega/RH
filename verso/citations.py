"""Write a proof by reference for wrappers of an imported theorem."""

from collections import deque
from functools import lru_cache
from pathlib import Path
import re
from urllib.parse import urlencode

from proofs import COMMAND, DECLARATION_NAME, IMPORT, PLACEHOLDER, compact, extract_claims, mask_non_code


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
BRACKETS = {"(": ")", "{": "}", "[": "]", "⦃": "⦄", "⟨": "⟩"}
DELIMITER = re.compile(r"[(){}\[\]⦃⦄⟨⟩]")
EXPLICIT = re.compile(rf"\(\s*({IDENTIFIER})\s*:\s*(.+?)\s*\)")
CONTEXTUAL = re.compile(r":=|[‹›]|\b(?:by|haveI?|letI?|match|show)\b")
BARE_PREMISE = re.compile(r"→|->|[∀∃λ,;|:]|\b(?:fun|if|do|calc|nomatch)\b")


def signature(source, masked, claim):
    command = COMMAND.match(masked, claim.start)
    name = DECLARATION_NAME.match(source, command.end())
    if name is None or QUOTED.search(source, name.end(), claim.statement_end):
        return None
    return compact(masked[name.end():claim.statement_end]) or None


def leading_binders(text):
    groups = deque()
    while text and text[0] in BRACKETS:
        closing = []
        for delimiter in DELIMITER.finditer(text):
            symbol = delimiter[0]
            if symbol in BRACKETS:
                closing.append(BRACKETS[symbol])
            elif closing.pop() != symbol:
                return groups, text
            if not closing:
                end = delimiter.end()
                groups.append(text[:end])
                text = text[end:].lstrip()
                break
        else:
            break
    return groups, text


def expose_quantifier(groups, body):
    if not groups and body.startswith("∀"):
        binders, tail = leading_binders(body[1:].lstrip())
        if binders and tail.startswith(","):
            return binders, tail[1:].lstrip()
    return groups, body


def after_premise(binder, groups, conclusion, body):
    match = EXPLICIT.fullmatch(binder)
    if match is None:
        return ""
    name, proposition = match.groups()
    if re.search(rf"(?<![\w'’]){re.escape(name)}(?![\w'’])", " ".join([*groups, conclusion])):
        return ""
    forms = [f"({proposition})"]
    if not BARE_PREMISE.search(proposition):
        forms.append(proposition)
    for form in forms:
        for arrow in (" → ", " -> "):
            if body.startswith(form + arrow):
                return body[len(form + arrow):]
    return ""


def same_quantified_statement(left, right):
    """Compare the ordered binders and conclusion without elaborating either term."""
    if CONTEXTUAL.search(left) or CONTEXTUAL.search(right):
        return False
    left_groups, lhs = leading_binders(left)
    right_groups, rhs = leading_binders(right)
    if not lhs.startswith(":") or not rhs.startswith(":"):
        return False
    lhs, rhs = lhs[1:].lstrip(), rhs[1:].lstrip()
    while left_groups or right_groups or lhs != rhs:
        left_groups, lhs = expose_quantifier(left_groups, lhs)
        right_groups, rhs = expose_quantifier(right_groups, rhs)
        if not left_groups:
            left_groups, right_groups = right_groups, left_groups
            lhs, rhs = rhs, lhs
        if not left_groups:
            return False
        binder = left_groups.popleft()
        if right_groups:
            if binder != right_groups.popleft():
                return False
        else:
            rhs = after_premise(binder, left_groups, lhs, rhs)
            if not rhs:
                return False
    return True


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
            reason = "The imported theorem has the same written statement and gives the conclusion directly."
        elif same_quantified_statement(statement, other_statement):
            reason = "The parameters and hypotheses occur in the same order in both statements, and the conclusions agree."
        else:
            continue
        query = urlencode({"module": module.as_posix(), "line": line})
        yield claim.start, (
            f"Apply the cited theorem to the given parameters and hypotheses. {reason}"
            f"\n\n[Source theorem](?{query}#L{line})"
        )
