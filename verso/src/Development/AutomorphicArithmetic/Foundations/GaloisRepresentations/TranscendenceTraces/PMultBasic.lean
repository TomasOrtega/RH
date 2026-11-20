import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `h1 h2 h3`. Conclude with `⟨h1, h2, h3⟩`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.multBasic_of :
    MultBC → MultOpen → MultEt → MultBasic := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩
