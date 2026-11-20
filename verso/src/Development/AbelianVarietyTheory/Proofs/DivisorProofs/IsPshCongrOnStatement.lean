import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPshCongrOn
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsPshCongrOn.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.isPsh_congr_divisor : ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ ψ : (Fin D → ℂ) → ℝ), ReciprocityTheory.AnForm.A.IsPsh U φ → (∀ z ∈ U, φ z = ψ z) → ReciprocityTheory.AnForm.A.IsPsh U ψ := by
  first | exact @GlobalTheory.isPsh_congr_on | exact GlobalTheory.isPsh_congr_on | (intros; apply GlobalTheory.isPsh_congr_on <;> assumption)
