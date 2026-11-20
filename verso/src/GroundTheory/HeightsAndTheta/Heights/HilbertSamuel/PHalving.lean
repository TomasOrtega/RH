import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Topology

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem Halving.eventually_le (a : ℕ → ℝ) (C : ℝ) (hC : ∀ n, |a n| ≤ C)
    (hh : Tendsto (fun n ↦ a (2 * n) - a n / 2) atTop (𝓝 0))
    (hs : Tendsto (fun n ↦ a (n + 1) - a n) atTop (𝓝 0)) (k : ℕ) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n| ≤ C / 2 ^ k + ε := by
  induction k with
  | zero =>
    intro ε hε
    exact ⟨0, fun n _ ↦ by simpa using (hC n).trans (by linarith)⟩
  | succ k ih =>
    intro ε hε
    obtain ⟨N, hN⟩ := ih (ε / 4) (by positivity)
    obtain ⟨M₁, hM₁⟩ := Metric.tendsto_atTop.mp hh (ε / 4) (by positivity)
    obtain ⟨M₂, hM₂⟩ := Metric.tendsto_atTop.mp hs (ε / 4) (by positivity)
    refine ⟨2 * (N + M₁ + M₂), fun m hm ↦ ?_⟩
    have hpow : C / 2 ^ (k + 1) = C / 2 ^ k / 2 := by rw [pow_succ, div_div]

    have even : ∀ n ≥ N + M₁ + M₂, |a (2 * n)| ≤ C / 2 ^ (k + 1) + ε / 2 := by
      intro n hn
      have h1 := hN n (by omega)
      have h2 := hM₁ n (by omega)
      rw [Real.dist_eq, sub_zero] at h2
      have h3 : |a (2 * n)| ≤ |a (2 * n) - a n / 2| + |a n| / 2 := by
        have := abs_add_le (a (2 * n) - a n / 2) (a n / 2)
        rw [sub_add_cancel, abs_div, abs_two] at this
        exact this
      rw [hpow]
      linarith
    obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
    · exact (even n (by omega)).trans (by linarith)
    · have he := even n (by omega)
      have h4 := hM₂ (2 * n) (by omega)
      rw [Real.dist_eq, sub_zero] at h4
      have h5 : |a (2 * n + 1)| ≤ |a (2 * n + 1) - a (2 * n)| + |a (2 * n)| := by
        have := abs_add_le (a (2 * n + 1) - a (2 * n)) (a (2 * n))
        rwa [sub_add_cancel] at this
      linarith

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem Halving.proof : Halving.Statement := by
  intro a ⟨C, hC⟩ hh hs
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, C / 2 ^ k < ε / 2 := by
    have ht : Tendsto (fun k : ℕ ↦ C / 2 ^ k) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, ← inv_pow] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num)).const_mul C
    exact (ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))).exists
  obtain ⟨N, hN⟩ := Halving.eventually_le a C hC hh hs k (ε / 4) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero]
  linarith [hN n hn]

end GroundTheory.Heights₂.Heights.HilbertSamuel
