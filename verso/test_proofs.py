import unittest

from proofs import explain, extract_claims, mask_non_code


class NaturalLanguageTests(unittest.TestCase):
    def outline(self, body):
        source = f"theorem claim (x : Nat) : x = x := {body}\n"
        masked = mask_non_code(source)
        [claim] = extract_claims(source, masked)
        status, prose = explain(source, masked, claim)
        self.assertEqual(status, "translation")
        return prose

    def test_tactics_do_not_copy_source_arguments(self):
        body = "by\n  have h := Wrapped.source_fact x\n  rw [← h, Function.comp_apply] at *\n  exact HIDDEN_TERM x"
        prose = self.outline(body)
        self.assertIn("intermediate fact", prose)
        self.assertIn("Rewrite the hypotheses and the conclusion", prose)
        for lean in ("Wrapped.source_fact", "Function.comp_apply", "HIDDEN_TERM", "\x60", ":="):
            self.assertNotIn(lean, prose)

    def test_unknown_direct_proof_reports_an_incomplete_outline(self):
        prose = self.outline("OpaqueTerm.authoring_required x")
        self.assertIn("derivation is pending", prose)
        self.assertNotIn("OpaqueTerm", prose)

    def test_function_proof_describes_the_logical_steps(self):
        prose = self.outline("fun h ↦ False.elim h")
        self.assertIn("hypotheses", prose)
        self.assertIn("contradiction", prose)
        self.assertNotIn("False.elim", prose)


if __name__ == "__main__":
    unittest.main()
