import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockNormBoundsMulXPderiv
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFockNormBoundsMulXPderiv.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.fock_norm_bounds_mul_X_pderiv : ∀ (σ : Type) [DecidableEq σ] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : MvPolynomial σ ℂ →ₗ[ℂ] H), IsFockIP ι → ∀ (i : σ) (d : ℕ) (P : MvPolynomial σ ℂ), P.totalDegree ≤ d → ‖ι (X i * P)‖ ^ 2 ≤ ((d : ℝ) + 1) * ‖ι P‖ ^ 2 ∧ ‖ι (pderiv i P)‖ ^ 2 ≤ (d : ℝ) * ‖ι P‖ ^ 2 := by
  first | exact @GlobalTheory.FockNormBound.fock_norm_bounds | exact GlobalTheory.FockNormBound.fock_norm_bounds | (intros; apply GlobalTheory.FockNormBound.fock_norm_bounds <;> assumption)
