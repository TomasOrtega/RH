import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatModPSquaredTorsion
open GlobalTheory GlobalTheory.DI
/- English proof (citation)
Apply `GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlatModPSquaredTorsion.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.flat_mod_p_squared_torsion : ∀ (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (φ : ZMod (p ^ 2) →+* B), φ.Flat → ∀ w : B, (p : B) * w = 0 ↔ ∃ v, w = p * v := by
  first | exact @_root_.GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff | exact _root_.GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff | (intros; apply _root_.GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff <;> assumption)
