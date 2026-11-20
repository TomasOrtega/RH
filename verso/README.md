# Verso proof archive

The Lean code in `src/` comes from `extracted/lean/src/`. English proof comments precede the declarations they describe. The site links each note to its statement, Lean proof, and original source line.

Written explanations present the mathematical argument in natural language. Proofs by reference link to the imported theorem and explain how its parameters, hypotheses, and conclusion match. English outlines identify steps that can be recovered from the source, such as induction, rewriting, and extensionality, and serve as drafts for the remaining full proofs. The site shows Lean in the statement and source panels. A source-gap note flags a declaration for which the text scan cannot identify a proof body.

Build the site from this directory with the pinned Lean toolchain and Python 3.10 or later.

```sh
lake build VersoManual
lake env lean --run Render.lean
python3 -B build_site.py
```

The last command checks that removing the proof comments recovers every extracted file byte for byte. It also checks that each identified theorem, lemma, example, and axiom has a note. The static site is in `_out/html-single/`.

To regenerate the comments, run `python3 -B annotate.py`. It reads the original files and the written explanations in `authored.json`. Pass module paths such as `Main.lean` to regenerate only those files.
