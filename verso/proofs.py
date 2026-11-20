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
IMPORT = re.compile(r"^[ \t]*(?:(?:public|meta) +)*import +(?:all +)?(\S+)", re.MULTILINE)
NOTE = re.compile(r"^/- English proof \((authored|citation|translation|source gap)\)\n(.*?)\n-/\n", re.MULTILINE | re.DOTALL)


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


PROOF_ACTIONS = {
    "abel": "Normalize the expressions using the abelian group laws.",
    "ac_rfl": "The two sides agree by associativity and commutativity.",
    "aesop": "Search for a derivation from the available facts and logical rules.",
    "apply": "Reduce the claim to the hypotheses of an applicable result.",
    "apply_rules": "Apply available rules repeatedly to reduce the claim to their hypotheses.",
    "assumption": "Use the matching hypothesis.",
    "by_cases": "Consider separately whether the proposition holds or fails.",
    "by_contra": "Assume the negation of the conclusion and derive a contradiction.",
    "case": "Treat this case separately.",
    "cases": "Split into cases according to the possible forms of the given data.",
    "change": "Express the relevant assertion in an equivalent form by its definition.",
    "congr": "Reduce the equality to equality of the corresponding arguments.",
    "constructor": "Prove the components needed by the constructor for the conclusion.",
    "contradiction": "The hypotheses give a contradiction.",
    "convert": "Apply an available result and prove the equalities needed to match it to the conclusion.",
    "decide": "Evaluate the decidable proposition.",
    "dsimp": "Simplify by unfolding definitions.",
    "exact?": "Find a matching proof by searching the available lemmas.",
    "exfalso": "It suffices to derive a contradiction.",
    "ext": "By extensionality, compare the relevant components.",
    "field_simp": "Clear the denominators using the available nonvanishing facts.",
    "finish": "Complete the remaining goals with the available hypotheses and lemmas.",
    "funext": "Apply function extensionality and compare values at an arbitrary argument.",
    "generalize": "Replace the chosen expression with an arbitrary variable.",
    "have": "Establish an intermediate fact.",
    "induction": "Proceed by induction.",
    "intro": "Fix the arbitrary inputs or assume the hypotheses.",
    "intros": "Fix the arbitrary inputs and assume the hypotheses.",
    "let": "Introduce a local definition for the expression.",
    "letI": "Equip the data with the indicated structure.",
    "linarith": "Combine the linear equalities and inequalities to obtain the conclusion.",
    "linear_combination": "Take a linear combination of the given relations to obtain the conclusion.",
    "native_decide": "Evaluate the decision procedure for the proposition.",
    "nlinarith": "Use the polynomial consequences of the given equalities and inequalities.",
    "norm_cast": "Put the expressions in a common number system so they can be compared.",
    "norm_num": "Evaluate the numerical expressions.",
    "obtain": "Extract witnesses or component facts from the available result.",
    "omega": "Use linear arithmetic over natural numbers and integers.",
    "positivity": "Check the signs of the components of the expression.",
    "push_cast": "Move the embeddings inside the algebraic operations.",
    "rcases": "Separate the alternatives or extract the components of the hypothesis.",
    "refine": "Reduce the conclusion to the remaining proof obligations.",
    "rfl": "Both sides reduce to the same expression.",
    "rintro": "Assume the hypotheses and unpack their components.",
    "ring": "Expand and normalize the polynomial expressions, which then agree.",
    "ring_nf": "Put the polynomial expressions in normal form.",
    "simp": "Simplify using the standard rewrite rules.",
    "simp_all": "Simplify the hypotheses and the goal together.",
    "simpa": "Simplify to obtain the desired conclusion from the available facts.",
    "specialize": "Apply the general hypothesis to the chosen values.",
    "subst": "Substitute using the available equality.",
    "suffices": "Reduce the argument to an intermediate assertion.",
    "symm": "Use symmetry to reverse the relation.",
    "tauto": "The claim follows by propositional logic.",
    "trivial": "Check the elementary cases of the proposition.",
    "unfold": "Replace the relevant objects with their definitions.",
    "use": "Choose witnesses for the existential claim.",
}
PENDING = "A detailed English derivation is pending."
NO_PROOF_STEP = {"classical", "rename_i", "skip"}
INTRODUCE = "Fix the arbitrary inputs and assume any hypotheses."
STEP = re.compile(r"^(?P<name>[\w_]+[!?]?)(?:\s+(?P<args>.*))?$")
SEQUENCE_TOKEN = re.compile(r"[({\[⟨⦃)}\]⟩⦄;]")


def term_prose(term):
    introductions = False
    while term.startswith("fun "):
        parts = re.split(r"=>|↦", term, maxsplit=1)
        if len(parts) != 2:
            break
        introductions = True
        term = parts[1].strip()
    if term == "rfl":
        conclusion = PROOF_ACTIONS["rfl"]
    elif term == "Iff.rfl":
        conclusion = "Unfold both sides to obtain the same proposition, which implies itself."
    elif term.startswith("False.elim "):
        conclusion = "The hypotheses yield a contradiction, which proves the conclusion."
    elif term.startswith(("And.intro ", "Iff.intro ")):
        conclusion = "Prove both required implications or components."
    elif term.startswith(("Exists.intro ", "⟨")):
        conclusion = "Supply the required witnesses or components."
    elif term.startswith("Or.inl "):
        conclusion = "Prove the first alternative."
    elif term.startswith("Or.inr "):
        conclusion = "Prove the second alternative."
    elif term.startswith("calc "):
        conclusion = "Chain the equalities or inequalities of the calculation."
    else:
        conclusion = PENDING
    return f"{INTRODUCE} {conclusion}" if introductions else conclusion


def describe_step(step):
    if step.startswith("|"):
        return "Treat this case separately."
    if step.startswith("calc "):
        return "Chain the equalities or inequalities of the calculation."
    if "<;>" in step:
        return "Apply the first step, then apply the next step to every resulting obligation."
    match = STEP.fullmatch(step)
    if match is None:
        return PENDING
    name = match["name"]
    args = match["args"] or ""
    if name in NO_PROOF_STEP:
        return ""
    if name == "exact":
        return term_prose(args)
    if name in {"rw", "rwa", "simp_rw"}:
        _, at, location = args.rpartition(" at ")
        if "*" in location or ("⊢" in location and len(location.split()) > 1):
            target = "the hypotheses and the conclusion"
        elif at and location != "⊢":
            target = "the indicated hypotheses"
        else:
            target = "the conclusion"
        if name == "simp_rw":
            return f"Rewrite {target} repeatedly using the stated equalities."
        follow = " Use the resulting assumption." if name == "rwa" else ""
        return f"Rewrite {target} using the stated equalities.{follow}"
    return PROOF_ACTIONS.get(name, PENDING)


def split_sequence(step):
    if ";" not in step or "<;>" in step or re.search(r"\bby\b", step):
        yield step
        return
    depth = 0
    start = 0
    for match in SEQUENCE_TOKEN.finditer(step):
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
    step = []
    indent = -1
    for line in body.splitlines():
        text = line.lstrip()
        if not text:
            continue
        visible_start = len(line) - len(text)
        bullet = text.startswith("·")
        text = text.removeprefix("·").strip()
        first = text.split(" ", 1)[0]
        starts_step = first in PROOF_ACTIONS or first in {"calc", "exact", "rw", "rwa", "simp_rw", "|"}
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
    body = masked[claim.proof_start:claim.end].strip()
    if not re.match(r"by\b", body):
        return "translation", term_prose(compact(body))
    sentences = [sentence for step in tactic_steps(body[2:]) if step and (sentence := describe_step(step))]
    if not sentences:
        return "translation", PENDING
    if PENDING in sentences:
        sentences = [sentence for sentence in sentences if sentence != PENDING] + [PENDING]
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
