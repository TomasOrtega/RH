import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarComplexGLMatricesConjAndSingularNull
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHaarComplexGLMatricesConjAndSingularNull.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.haarComplexGLMatrices_conj_and_singular_null : ∀ j : ℕ, MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => starRingEnd ℂ (x r s)) (haarLoc j) (haarLoc j) ∧ haarLoc j {x | (Matrix.of x).det = 0} = 0 := by
  first | exact @GlobalTheory.LeviIso.haarLoc_conj_and_null | exact GlobalTheory.LeviIso.haarLoc_conj_and_null | (intros; apply GlobalTheory.LeviIso.haarLoc_conj_and_null <;> assumption)
