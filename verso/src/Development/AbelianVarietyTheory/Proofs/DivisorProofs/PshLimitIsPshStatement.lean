import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshLimitIsPsh
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isPsh_of_tendsto_of_locally_bounded_above` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPshLimitIsPsh.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.psh_limit_is_psh : ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (φ : (Fin D → ℂ) → ℝ) (ψ : ℕ → (Fin D → ℂ) → ℝ) (V : ℕ → Set (Fin D → ℂ)), IsOpen U → UpperSemicontinuousOn φ U → (∀ n, ReciprocityTheory.AnForm.A.IsPsh (V n) (ψ n)) → (∀ K : Set (Fin D → ℂ), IsCompact K → K ⊆ U → ∃ N : ℕ, ∃ M : ℝ, ∀ n, N ≤ n → K ⊆ V n ∧ ∀ z ∈ K, ψ n z ≤ M) → (∀ z ∈ U, Filter.Tendsto (fun n => ψ n z) Filter.atTop (nhds (φ z))) → ReciprocityTheory.AnForm.A.IsPsh U φ := by
  first | exact @GlobalTheory.isPsh_of_tendsto_of_locally_bounded_above | exact GlobalTheory.isPsh_of_tendsto_of_locally_bounded_above | (intros; apply GlobalTheory.isPsh_of_tendsto_of_locally_bounded_above <;> assumption)
