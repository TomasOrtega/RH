import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryEqReflOfCongrModGeThree
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsometryEqReflOfCongrModGeThree.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.isometry_eq_refl_of_congr_mod_ge_three : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (β : LinearMap.BilinForm ℤ X), (∀ x, x ≠ 0 → 0 < β x x) → ∀ (e : X ≃ₗ[ℤ] X), (∀ x y, β (e x) (e y) = β x y) → ∀ N : ℕ, 3 ≤ N → (∀ x, CongMod N (e x) x) → e = LinearEquiv.refl ℤ X := by
  first | exact @GlobalTheory.Poinc.eq_refl_of_isometry_congMod | exact GlobalTheory.Poinc.eq_refl_of_isometry_congMod | (intros; apply GlobalTheory.Poinc.eq_refl_of_isometry_congMod <;> assumption)
