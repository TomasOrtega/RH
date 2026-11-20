import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalHarishChandraFiniteFormBoundedDetNormBan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HCF.bounded_on_band_of_cuspidal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCuspidalHarishChandraFiniteFormBoundedDetNormBan.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.cuspidal_harishChandraFiniteForm_bounded_detNormBand : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), IsCuspidal φ.1 → ∃ M : ℝ, ∀ g ∈ band E a, ‖φ.1 g‖ ≤ M := by
  first | exact @GlobalTheory.HCF.bounded_on_band_of_cuspidal | exact GlobalTheory.HCF.bounded_on_band_of_cuspidal | (intros; apply GlobalTheory.HCF.bounded_on_band_of_cuspidal <;> assumption)
