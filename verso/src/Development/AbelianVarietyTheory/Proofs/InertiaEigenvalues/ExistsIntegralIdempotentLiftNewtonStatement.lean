import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralIdempotentLiftNewton
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommOfBezout
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsIntegralIdempotentLiftNewton.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.exists_integral_idempotent_lift_newton : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [CompleteSpace E] (n : ℕ) (N x a : Matrix (Fin n) (Fin n) E) (ϖ : E), ‖ϖ‖ < 1 → x * N = N * x → (∀ i j, ‖x i j‖ ≤ 1) → (∀ i j, ‖a i j‖ ≤ 1) → x * x - x = ϖ • a → ∃ e a' : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a' * N = N * a' ∧ e * e = e ∧ (∀ i j, ‖e i j‖ ≤ 1) ∧ (∀ i j, ‖a' i j‖ ≤ 1) ∧ e - x = ϖ • a' := by
  first | exact @GlobalTheory.IdemLift.idem_lift | exact GlobalTheory.IdemLift.idem_lift | (intros; apply GlobalTheory.IdemLift.idem_lift <;> assumption)
