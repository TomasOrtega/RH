import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem UpperTheory.Gal.TranscendenceTraces.multBasic_of :
    MultBC → MultOpen → MultEt → MultBasic := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩
