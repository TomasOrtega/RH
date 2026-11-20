import Mathlib

namespace GlobalTheory.PowerNearOneNorm

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem exists_pow_sub_one_norm_lt_one {p : ℕ} [hp : Fact (Nat.Prime p)] (x : PadicAlgCl p)
    (hx : ‖x‖ = (1 : ℝ)) : ∃ n : ℕ, 0 < n ∧ ‖x ^ n - (1 : PadicAlgCl p)‖ < (1 : ℝ) := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  let V : Submodule ℚ_[p] (PadicAlgCl p) := Subalgebra.toSubmodule (Algebra.adjoin ℚ_[p] {x})
  have : FiniteDimensional ℚ_[p] V := Module.Finite.iff_fg.mpr hint.fg_adjoin_singleton
  have : ProperSpace V := FiniteDimensional.proper ℚ_[p] V
  have hmem : ∀ n : ℕ, x ^ n ∈ V := fun n =>
    Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℚ_[p] x) n
  let s : ℕ → V := fun n => ⟨x ^ n, hmem n⟩
  have hs : ∀ n, s n ∈ Metric.closedBall (0 : V) 1 := by
    intro n
    simp [s, norm_pow, hx]
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : V) 1).tendsto_subseq hs
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq 1 one_pos
  have h1 := hN (N + 1) (Nat.le_succ N)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (hφ (Nat.lt_succ_self N))
  refine ⟨d + 1, d.succ_pos, ?_⟩
  have e : x ^ φ (N + 1) - x ^ φ N = x ^ φ N * (x ^ (d + 1) - 1) := by
    rw [hd]
    ring
  have h1' : ‖x ^ φ (N + 1) - x ^ φ N‖ < 1 := by simpa [s, dist_eq_norm] using h1
  rwa [e, norm_mul, norm_pow, hx, one_pow, one_mul] at h1'

end GlobalTheory.PowerNearOneNorm
