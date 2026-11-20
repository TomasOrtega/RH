import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryCharPiComplexUnitsEqProdZpow
open scoped Topology BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FUnitaryCharPiComplexUnitsEqProdZpow.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.exists_zpow_prod_div_conj_of_continuous_trivial_on_real : ∀ (ι : Type) [Fintype ι] (f : (ι → ℂˣ) →* Circle), Continuous f → (∀ z : ι → ℂˣ, (∀ i, ((z i : ℂ)).im = 0) → f z = 1) → ∃ k : ι → ℤ, ∀ z, ((f z : Circle) : ℂ) = ∏ i, ((z i : ℂ) / starRingEnd ℂ (z i : ℂ)) ^ k i := by
  first | exact @GlobalTheory.unitaryChar_pi_complexUnits_eq_prod_zpow | exact GlobalTheory.unitaryChar_pi_complexUnits_eq_prod_zpow | (intros; apply GlobalTheory.unitaryChar_pi_complexUnits_eq_prod_zpow <;> assumption)
