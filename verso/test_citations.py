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


if __name__ == "__main__":
    unittest.main()
