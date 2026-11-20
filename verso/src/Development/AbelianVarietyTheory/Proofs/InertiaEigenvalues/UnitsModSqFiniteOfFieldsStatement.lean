import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsModSqFiniteOfFields
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.units_modSq_finite_of_fields` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnitsModSqFiniteOfFields.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.finite_units_mod_sq_of_finite_for_fields : ∀ (k : Type) [Field k] [CharZero k], (∀ (L : Type) [Field L] [Algebra k L] [FiniteDimensional k L], Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range)) → ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], Finite (Aˣ ⧸ (powMonoidHom 2 : Aˣ →* Aˣ).range) := by
  first | exact @GlobalTheory.units_modSq_finite_of_fields | exact GlobalTheory.units_modSq_finite_of_fields | (intros; apply GlobalTheory.units_modSq_finite_of_fields <;> assumption)
