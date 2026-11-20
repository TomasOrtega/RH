# Verso proof archive

The Lean code in `src/` comes from `extracted/lean/src/`. English proof comments precede the declarations they describe. The site links each note to its statement, Lean proof, and original source line.

Written explanations state the mathematical argument directly. Source translations describe the proof steps visible in Lean. For automation tactics, the translations identify the method or tactic, since the intermediate derivations require elaboration. A source-gap note flags a declaration for which the text scan cannot identify a proof body.

Build the site from this directory with the pinned Lean toolchain and Python 3.10 or later.

```sh
lake build VersoManual
lake env lean --run Render.lean
python3 -B build_site.py
```

The last command checks that removing the proof comments recovers every extracted file byte for byte. It also checks that each identified theorem, lemma, example, and axiom has a note. The static site is in `_out/html-single/`.

To regenerate the comments, run `python3 -B annotate.py`. It reads the original files and the written explanations in `authored.json`. Pass module paths such as `Main.lean` to regenerate only those files.
