from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

import annotate
from proofs import remove_notes


class AuthoredNotesTests(unittest.TestCase):
    def test_same_named_claims_can_have_distinct_notes(self):
        source = (
            "namespace First\n"
            "theorem shared : True := trivial\n"
            "end First\n"
            "namespace Second\n"
            "theorem shared : 0 = 0 := rfl\n"
            "theorem unique : 1 = 1 := rfl\n"
            "end Second\n"
        )
        explanations = {
            "shared:2": "Truth holds by its defining witness.",
            "shared:5": "Zero equals itself by reflexivity.",
            "unique": "One equals itself by reflexivity.",
        }
        with TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "original").mkdir()
            (root / "original" / "Test.lean").write_text(source)
            with (
                patch.object(annotate, "EXTRACTED", root / "original"),
                patch.object(annotate, "COPY", root / "copy"),
                patch.object(annotate, "AUTHORED", {"Test.lean": explanations}),
            ):
                counts = annotate.annotate_module("Test.lean")
            stripped, notes = remove_notes((root / "copy" / "Test.lean").read_text())

        self.assertEqual(counts, {"modules": 1, "authored": 3})
        self.assertEqual(stripped, source)
        self.assertEqual([(status, prose) for _, status, prose in notes], [
            ("authored", prose) for prose in explanations.values()
        ])
