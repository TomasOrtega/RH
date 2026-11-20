import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTaylorPartialSumDerivBound
import Mathlib
open SchwartzMap Filter Topology
open scoped Nat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzTaylorPartialSumDerivBound.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.schwartz_taylor_partial_sum_deriv_bound : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ψ : SchwartzMap V ℂ) (A ρ : ℝ), (∀ (j : ℕ) (y : V), ‖iteratedFDeriv ℝ j ψ y‖ ≤ A * ρ ^ j) →
    ∀ (m a : ℕ) (x : V), ‖iteratedFDeriv ℝ a (fun y => ∑ j ∈ Finset.range (m + 1),
      ((j ! : ℝ))⁻¹ • iteratedFDeriv ℝ j ψ 0 (fun _ => y)) x‖ ≤ |A| * |ρ| ^ a * Real.exp (|ρ| * ‖x‖) := by
  first | exact @GlobalTheory.taylorPoly_iteratedFDeriv_le | exact GlobalTheory.taylorPoly_iteratedFDeriv_le | (intros; apply GlobalTheory.taylorPoly_iteratedFDeriv_le <;> assumption)
