"""Extract proof declarations and describe their source-level arguments."""

from dataclasses import dataclass
import re


NON_CODE = re.compile(
    r'/-|--[^\r\n]*|r(?P<hashes>#+)".*?"(?P=hashes)|"(?:\\.|[^"\\])*"|«[^»]*»',
    re.DOTALL,
)
COMMENT_DELIMITER = re.compile(r"/-|-/")
COMMAND = re.compile(
    r"^(?P<indent>[ \t]*)(?:(?:@\[[^\n]*\]|(?:set_option|open)[ \t]+[^\n]*?\bin)[ \t]+)*"
    r"(?:(?:public|private|protected|noncomputable|unsafe|local|scoped|partial) +)*"
    r"(?P<kind>theorem|lemma|example|axiom|def|abbrev|opaque|instance|class|structure|inductive"
    r"|namespace|section|end|open|variable|universe|set_option|attribute|import|include|omit"
    r"|syntax|macro|notation|infix[lr]?|module|mutual|export)(?=\s|$)"
    r"|^(?P<hash_indent>[ \t]*)#(?:check|eval|print|reduce|synth|guard|guard_msgs|lint)(?=\s|$)",
    re.MULTILINE,
)
DECLARATION_NAME = re.compile(r"[ \t]*(«[^»]*»|[^\s({\[⦃⟨:]+)")
CLAIM_KINDS = {"theorem", "lemma", "example", "axiom"}
BODY_TOKEN = re.compile(r":=|\b(?:let|letI|have)\b|[({\[⟨⦃)}\]⟩⦄]|^[ \t]*\|", re.MULTILINE)
PLACEHOLDER = re.compile(r"\b(?:sorry|admit|sorryAx)\b")
NOTE = re.compile(r"^/- English proof \((authored|translation|source gap)\)\n(.*?)\n-/\n", re.MULTILINE | re.DOTALL)


@dataclass(frozen=True)
class Claim:
    start: int
    end: int
    line: int
    kind: str
    name: str
    statement_end: int
    proof_start: int | None


def mask_non_code(source):
    """Blank comments and literals, keeping offsets and line starts."""
    parts = []
    cursor = 0
    while match := NON_CODE.search(source, cursor):
        end = match.end()
        if match[0] == "/-":
            depth = 1
            for delimiter in COMMENT_DELIMITER.finditer(source, end):
                depth += 1 if delimiter[0] == "/-" else -1
                if depth == 0:
                    end = delimiter.end()
                    break
            else:
                end = len(source)
        parts.append(source[cursor:match.start()])
        parts.append(re.sub(r"[^\r\n]", " ", source[match.start():end]))
        cursor = end
    parts.append(source[cursor:])
    return "".join(parts)


def find_body(masked, start, end):
    depth = 0
    bindings = 0
    for token in BODY_TOKEN.finditer(masked, start, end):
        text = token[0]
        if text in "({[⟨⦃":
            depth += 1
        elif text in ")}]⟩⦄":
            depth = max(0, depth - 1)
        elif depth == 0:
            if text in {"let", "letI", "have"}:
                bindings += 1
            elif text == ":=":
                if bindings == 0:
                    return token.start(), token.end()
                bindings -= 1
            elif text.endswith("|"):
                return token.start(), token.start()
    return end, None


def extract_claims(source, masked=None):
    if masked is None:
        masked = mask_non_code(source)
    commands = list(COMMAND.finditer(masked))
    line = 1
    previous_start = 0
    for index, command in enumerate(commands):
        kind = command["kind"]
        if kind not in CLAIM_KINDS:
            continue
        start = command.start()
        line += source.count("\n", previous_start, start)
        previous_start = start
        indent = len(command["indent"])
        end = len(source)
        for next_index in range(index + 1, len(commands)):
            following = commands[next_index]
            if len(following["indent"] or following["hash_indent"] or "") <= indent:
                end = following.start()
                break
        while end > command.end() and source[end - 1].isspace():
            end -= 1
        name_match = DECLARATION_NAME.match(source, command.end())
        name = name_match[1] if name_match and kind != "example" else kind
        statement_end, proof_start = find_body(masked, command.end(), end)
        yield Claim(start, end, line, kind, name, statement_end, proof_start)


def compact(text):
    return " ".join(text.split())


def code(text, limit=280):
    text = compact(text).replace("\x60", "′")
    if len(text) > limit:
        text = text[:limit].rstrip() + " …"
    return f"\x60{text}\x60"


NO_ARGUMENT_TACTICS = {
    "abel": "Normalize the expressions using the abelian group laws.",
    "ac_rfl": "The two sides agree by associativity and commutativity.",
    "aesop": "Discharge the remaining goals by the proof search in \x60aesop\x60.",
    "assumption": "Use the matching hypothesis.",
    "by_contra": "Assume the negation of the conclusion and derive a contradiction.",
    "congr": "Reduce the equality to equality of the corresponding arguments.",
    "constructor": "Prove the components needed by the constructor for the conclusion.",
    "contradiction": "The hypotheses give a contradiction.",
    "decide": "Evaluate the decidable proposition.",
    "exact?": "Find a matching proof by searching the available lemmas.",
    "exfalso": "It suffices to derive a contradiction.",
    "field_simp": "Clear the denominators using the available nonvanishing facts.",
    "finish": "Complete the remaining goals with the available hypotheses and lemmas.",
    "funext": "Apply function extensionality and compare values at an arbitrary argument.",
    "linarith": "Combine the linear equalities and inequalities to obtain the conclusion.",
    "native_decide": "Evaluate the decision procedure for the proposition.",
    "nlinarith": "Use the polynomial consequences of the given equalities and inequalities.",
    "norm_num": "Evaluate the numerical expressions.",
    "omega": "Use linear arithmetic over natural numbers and integers.",
    "positivity": "Check the signs of the components of the expression.",
    "rfl": "Both sides reduce to the same expression.",
    "ring": "Expand and normalize the polynomial expressions, which then agree.",
    "ring_nf": "Put the polynomial expressions in normal form.",
    "simp": "Simplify using the standard rewrite rules.",
    "simp_all": "Simplify the hypotheses and the goal together.",
    "tauto": "The claim follows by propositional logic.",
    "trivial": "Discharge the goal by the elementary cases of \x60trivial\x60.",
}

TACTIC_ARGUMENTS = {
    "apply": "Apply {} to reduce the goal to its premises.",
    "apply_rules": "Repeatedly apply the rules in {}.",
    "by_cases": "Distinguish the cases in {}.",
    "by_contra": "Assume the negation of the conclusion as {}.",
    "cases": "Consider the cases of {}.",
    "change": "Express the relevant statement in the definitionally equal form {}.",
    "convert": "Use {} and compare the differences between its conclusion and the goal.",
    "exact": "Conclude with {}.",
    "exact_mod_cast": "Conclude with {} after adjusting the coercions.",
    "ext": "Use extensionality with {}.",
    "field_simp": "Clear denominators, using {} for the nonvanishing conditions.",
    "funext": "Use function extensionality and compare the values at {}.",
    "generalize": "Generalize the expression as in {}.",
    "induction": "Proceed by induction on {}.",
    "intro": "Introduce {}.",
    "intros": "Introduce {}.",
    "linarith": "Combine the linear relations using {}.",
    "linear_combination": "Take the linear combination {}.",
    "nlinarith": "Use polynomial arithmetic with {}.",
    "norm_cast": "Normalize the coercions in {}.",
    "norm_num": "Evaluate the numerical expressions using {}.",
    "obtain": "Choose the witnesses or unpack the hypotheses as in {}.",
    "push_cast": "Move the coercions through the operations in {}.",
    "rcases": "Break down {} into its components or cases.",
    "refine": "Use {} and prove the remaining obligations.",
    "rename_i": "Name the introduced variables {}.",
    "repeat": "Repeat the step {} while it applies.",
    "rintro": "Introduce and unpack {}.",
    "rw": "Rewrite using {}.",
    "rwa": "Rewrite using {} and apply the resulting hypothesis.",
    "simp_rw": "Repeatedly rewrite using {}.",
    "specialize": "Specialize {}.",
    "subst": "Substitute {} using the available equality.",
    "symm": "Use symmetry as in {}.",
    "unfold": "Unfold {}.",
    "use": "Choose the witnesses {}.",
}

STEP = re.compile(r"^(?P<name>[\w_]+[!?]?)(?:\s+(?P<args>.*))?$")
SEQUENCE_TOKEN = re.compile(r"[({\[⟨⦃)}\]⟩⦄;]")


def term_prose(term):
    term = compact(term)
    if term == "Iff.rfl":
        return "Unfold both sides. The equivalence is reflexive."
    if term in NO_ARGUMENT_TACTICS:
        return NO_ARGUMENT_TACTICS[term]
    if term.startswith("False.elim "):
        return f"Derive the conclusion from the contradiction {code(term.removeprefix('False.elim '))}."
    if term.startswith("⟨"):
        return f"Assemble the required witnesses or components as {code(term)}."
    if term.startswith("fun ") and "=>" in term:
        binders, _, body = term[4:].partition("=>")
        return f"Introduce {code(binders)} and use {code(body)}."
    if term.startswith("calc "):
        return f"Combine the equalities or inequalities in the calculation {code(term)}."
    return f"The claim follows from {code(term)}."


def describe_step(step):
    if step.startswith("|"):
        case = step[1:].strip().removesuffix("=>").strip()
        return f"Consider the case {code(case)}." if case else ""
    if step.startswith("calc"):
        return "Combine the equalities or inequalities in the displayed calculation."
    if any(operator in step for operator in ("<;>", " <|> ", "first |", "all_goals ", "try ")):
        return f"Apply the tactic sequence {code(step)}."
    match = STEP.fullmatch(step)
    if match is None:
        return f"Use the proof step {code(step)}."
    name = match["name"]
    args = match["args"]
    if name in {"classical", "skip"}:
        return ""
    if not args and name in NO_ARGUMENT_TACTICS:
        return NO_ARGUMENT_TACTICS[name]
    if name in {"have", "suffices", "let"} and args:
        claim, separator, proof = args.partition(":=")
        if name == "have" and not claim.strip() and proof.strip() not in {"", "by"}:
            return f"Use {code(proof)} as an intermediate fact."
        if name == "let":
            return f"Set {code(claim)} to {code(proof)}." if proof else f"Introduce the local definition {code(claim)}."
        verb = "It suffices to establish" if name == "suffices" else "Establish"
        if separator and proof.strip() not in {"", "by"}:
            return f"{verb} {code(claim)} using {code(proof)}."
        return f"{verb} {code(claim)}." if claim.strip() else "Establish an intermediate fact."
    if name == "obtain" and args:
        witnesses, _, proof = args.partition(":=")
        if proof.strip() and proof.strip() != "by":
            return f"Take {code(witnesses)} from {code(proof)}."
    if name in {"simp", "simp_all", "simpa", "dsimp"} and args:
        rules, using, proof = args.partition(" using ")
        if using:
            return f"Simplify {code(proof)} using {code(rules)}." if rules else f"Simplifying {code(proof)} gives the conclusion."
        return f"Simplify using {code(rules)}."
    if name in {"rw", "rwa", "simp_rw"} and args:
        rules, at, location = args.rpartition(" at ")
        if at and re.fullmatch(r"[\w'.⊢* ]+", location):
            target = ", ".join("the goal" if item == "⊢" else code(item) for item in location.split())
            conclusion = " Then use the resulting hypothesis." if name == "rwa" else ""
            return f"Rewrite {target} using {code(rules)}.{conclusion}"
    if args and name in TACTIC_ARGUMENTS:
        return TACTIC_ARGUMENTS[name].format(code(args))
    return f"Use {code(step)}."


def split_sequence(step):
    if ";" not in step or "<;>" in step or re.search(r"\bby\b", step):
        yield step
        return
    depth = 0
    start = 0
    for match in SEQUENCE_TOKEN.finditer(mask_non_code(step)):
        char = match[0]
        if char in "({[⟨⦃":
            depth += 1
        elif char in ")}]⟩⦄":
            depth = max(0, depth - 1)
        elif depth == 0:
            yield step[start:match.start()].strip()
            start = match.end()
    yield step[start:].strip()


def tactic_steps(body):
    masked = mask_non_code(body)
    lines = body.split("\n")
    step = []
    indent = -1
    for original, visible in zip(lines, masked.split("\n")):
        if not visible.strip():
            continue
        visible_start = len(visible) - len(visible.lstrip())
        text = original[visible_start:].strip()
        bullet = text.startswith("·")
        text = text.removeprefix("·").strip()
        first = text.split(" ", 1)[0]
        starts_step = (
            first in TACTIC_ARGUMENTS
            or first in NO_ARGUMENT_TACTICS
            or first in {"have", "suffices", "let", "letI", "simpa", "calc", "case", "|"}
        )
        if step and (bullet or visible_start <= indent or starts_step):
            yield from split_sequence(compact(" ".join(step)))
            step = []
        if text:
            if not step:
                indent = visible_start
            step.append(text)
    if step:
        yield from split_sequence(compact(" ".join(step)))


def explain(source, masked, claim):
    if claim.kind == "axiom":
        return "source gap", "This declaration takes the statement as an axiom."
    if claim.proof_start is None:
        return "source gap", "The source scan could not identify a proof body for this declaration."
    body = source[claim.proof_start:claim.end].strip()
    if not body:
        return "source gap", "The declaration contains no proof body."
    if PLACEHOLDER.search(masked, claim.proof_start, claim.end):
        return "source gap", "The source contains an admitted step in this argument."
    if not re.match(r"by\b", body):
        return "translation", term_prose(body)
    sentences = [sentence for step in tactic_steps(body[2:]) if step and (sentence := describe_step(step))]
    if not sentences:
        return "translation", f"The proof uses {code(body)}."
    paragraphs = [" ".join(sentences[start:start + 5]) for start in range(0, len(sentences), 5)]
    return "translation", "\n\n".join(paragraphs)


def insert_notes(source, claims, notes):
    parts = []
    cursor = 0
    for claim, (status, prose) in zip(claims, notes):
        prose = prose.replace("/-", "/ -").replace("-/", "- /")
        parts.extend((source[cursor:claim.start], f"/- English proof ({status})\n{prose}\n-/\n"))
        cursor = claim.start
    parts.append(source[cursor:])
    return "".join(parts)


def remove_notes(source):
    parts = []
    notes = []
    cursor = 0
    offset = 0
    for match in NOTE.finditer(source):
        part = source[cursor:match.start()]
        parts.append(part)
        offset += len(part)
        notes.append((offset, match[1], match[2]))
        cursor = match.end()
    parts.append(source[cursor:])
    return "".join(parts), notes
