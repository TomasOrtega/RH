import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesEvalTruncSubstEqSum
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DivSub.eval_trunc'_subst_eq_sum` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMvPowerSeriesEvalTruncSubstEqSum.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.mvPowerSeries_eval_trunc_subst_eq_sum : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ τ : Type) [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] (z : σ → B) (u : τ → MvPowerSeries σ B), (∀ j, constantCoeff (u j) = 0) → ∀ (g : MvPowerSeries τ Q) (n : σ →₀ ℕ) (S : Finset (τ →₀ ℕ)), (∀ α : τ →₀ ℕ, α.degree ≤ n.degree → α ∈ S) → MvPolynomial.eval (fun i => algebraMap B Q (z i)) (trunc' Q n (subst (up Q u) g)) = ∑ α ∈ S, coeff α g * algebraMap B Q (MvPolynomial.eval z (trunc' B n (α.prod fun j e => u j ^ e))) := by
  first | exact @GlobalTheory.DivSub.eval_trunc'_subst_eq_sum | exact GlobalTheory.DivSub.eval_trunc'_subst_eq_sum | (intros; apply GlobalTheory.DivSub.eval_trunc'_subst_eq_sum <;> assumption)
