import tempfile
import unittest
from pathlib import Path

from citations import citations, exported_claims
from proofs import extract_claims, mask_non_code


WRAPPER = """import Supporting

theorem same (x : Nat) : x = x := by
  first | exact @Example.reflexive | exact Example.reflexive | (intros; apply Example.reflexive <;> assumption)
"""


class CitationTests(unittest.TestCase):
    def references(self, supporting, wrapper=WRAPPER):
        self.addCleanup(exported_claims.cache_clear)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Supporting.lean").write_text(supporting, encoding="utf-8")
            masked = mask_non_code(wrapper)
            return list(citations(root, wrapper, masked, extract_claims(wrapper, masked)))

    def test_anonymous_section_can_extend_to_end_of_file(self):
        supporting = """noncomputable section
namespace Example
theorem reflexive (x : Nat) : x = x := rfl
end Example
"""
        [(_, prose)] = self.references(supporting)
        self.assertIn("?module=Supporting.lean&line=3#L3", prose)

    def test_rejects_different_statement(self):
        supporting = """namespace Example
theorem reflexive (x : Nat) : x + 0 = x := Nat.add_zero x
end Example
"""
        self.assertEqual(self.references(supporting), [])

    def test_two_applications_of_the_same_theorem(self):
        supporting = """namespace Example
theorem reflexive (x : Nat) : x = x := rfl
end Example
"""
        wrapper = WRAPPER.rsplit(" | ", 1)[0]
        [(_, prose)] = self.references(supporting, wrapper)
        self.assertIn("?module=Supporting.lean&line=2#L2", prose)

    def test_rejects_distinct_alternative(self):
        supporting = """namespace Example
theorem reflexive (x : Nat) : x = x := rfl
end Example
"""
        self.assertEqual(self.references(supporting, WRAPPER.replace("apply Example.reflexive", "apply other")), [])

    def signatures(self, wrapper, target):
        supporting = f"namespace Example\ntheorem reflexive {target} := trivial\nend Example\n"
        return self.references(supporting, WRAPPER.replace("(x : Nat) : x = x", wrapper))

    def test_quantifiers_and_arrows_match_declaration_binders(self):
        [(_, prose)] = self.signatures(
            ": ∀ {α : Type} [LinearOrder α] (x : α), x ≤ x → ∀ (y : α), (∀ z : α, z ≤ y) → x ≤ y",
            "{α : Type} [LinearOrder α] (x : α) (hx : x ≤ x) (y : α) (hy : ∀ z : α, z ≤ y) : x ≤ y",
        )
        self.assertIn("?module=Supporting.lean&line=2#L2", prose)

    def test_rejects_a_different_binder_kind(self):
        self.assertEqual(self.signatures(": ∀ (x : Nat), x = x", "{x : Nat} : x = x"), [])

    def test_rejects_removing_a_binder_used_in_the_conclusion(self):
        self.assertEqual(self.signatures(": p → Q h", "(h : p) : Q h"), [])

    def test_rejects_removing_a_binder_used_in_a_later_hypothesis(self):
        self.assertEqual(
            self.signatures(": p → ∀ (x : T h), True", "(h : p) (x : T h) : True"),
            [],
        )

    def test_parentheses_separate_function_hypotheses(self):
        self.assertTrue(self.signatures(": (p → q) → True", "(h : p → q) : True"))
        self.assertEqual(self.signatures(": p → q → True", "(h : p → q) : True"), [])

    def test_rejects_left_hand_quantifier_with_unclosed_scope(self):
        self.assertEqual(self.signatures(": ∀ x, p x → True", "(h : ∀ x, p x) : True"), [])

    def test_rejects_optional_parameters(self):
        self.assertEqual(self.signatures(": Nat → True", "(x : Nat := 0) : True"), [])

    def test_rejects_anonymous_hypothesis_lookup(self):
        self.assertEqual(self.signatures(": p → Q ‹p›", "(h : p) : Q ‹p›"), [])


if __name__ == "__main__":
    unittest.main()
