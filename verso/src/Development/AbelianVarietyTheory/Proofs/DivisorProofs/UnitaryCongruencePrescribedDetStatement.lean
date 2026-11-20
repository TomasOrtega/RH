import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruencePrescribedDet
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.detfix_unitary_transvection` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryCongruencePrescribedDet.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.unitary_congruence_prescribed_det : ∀ {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (τ : R →+* R) (H : Matrix n n R) (e : n → R) (p u s : R) (k : ℕ), (∀ a, τ (τ a) = a) → Formalism.UG.cT τ H = H → IsUnit (Formalism.UG.hform τ H e e) → u * τ u = 1 → u = 1 + p ^ (k + 1) * s → ∃ g M : Matrix n n R, Formalism.UG.cT τ g * H * g = H ∧ g.det = u ∧ g = 1 + p ^ (k + 1) • M := by
  first | exact @GlobalTheory.detfix_unitary_transvection | exact GlobalTheory.detfix_unitary_transvection | (intros; apply GlobalTheory.detfix_unitary_transvection <;> assumption)
