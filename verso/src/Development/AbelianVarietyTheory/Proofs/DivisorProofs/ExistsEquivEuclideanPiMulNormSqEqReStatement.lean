import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivEuclideanPiMulNormSqEqRe
import Mathlib
open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsEquivEuclideanPiMulNormSqEqRe.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_euclidean_equiv_pi_mul_norm_sq_eq_re : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ),
    0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∃ A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re := by
  first | exact @GlobalTheory.exists_equiv_euclidean_pi_mul_norm_sq_eq_re | exact GlobalTheory.exists_equiv_euclidean_pi_mul_norm_sq_eq_re | (intros; apply GlobalTheory.exists_equiv_euclidean_pi_mul_norm_sq_eq_re <;> assumption)
