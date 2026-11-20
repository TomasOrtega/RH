import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Topology

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `ε hε`. Conclude with `⟨0, fun n _ ↦ by simpa using (hC n).trans (by linarith)⟩`. Consider the case `succ k ih`.

Introduce `ε hε`. Take `⟨N, hN⟩` from `ih (ε / 4) (by positivity)`. Take `⟨M₁, hM₁⟩` from `Metric.tendsto_atTop.mp hh (ε / 4) (by positivity)`. Take `⟨M₂, hM₂⟩` from `Metric.tendsto_atTop.mp hs (ε / 4) (by positivity)`. Use `⟨2 * (N + M₁ + M₂), fun m hm ↦ ?_⟩` and prove the remaining obligations.

Establish `hpow : C / 2 ^ (k + 1) = C / 2 ^ k / 2` using `by rw [pow_succ, div_div]`. Establish `even : ∀ n ≥ N + M₁ + M₂, |a (2 * n)| ≤ C / 2 ^ (k + 1) + ε / 2`. Introduce `n hn`. Establish `h1` using `hN n (by omega)`. Establish `h2` using `hM₁ n (by omega)`.

Rewrite `h2` using `[Real.dist_eq, sub_zero]`. Establish `h3 : |a (2 * n)| ≤ |a (2 * n) - a n / 2| + |a n| / 2`. Use `abs_add_le (a (2 * n) - a n / 2) (a n / 2)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, abs_div, abs_two]`. Conclude with `this`.

Rewrite using `[hpow]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨n, rfl | rfl⟩` from `Nat.even_or_odd' m`. Conclude with `(even n (by omega)).trans (by linarith)`. Establish `he` using `even n (by omega)`.

Establish `h4` using `hM₂ (2 * n) (by omega)`. Rewrite `h4` using `[Real.dist_eq, sub_zero]`. Establish `h5 : |a (2 * n + 1)| ≤ |a (2 * n + 1) - a (2 * n)| + |a (2 * n)|`. Use `abs_add_le (a (2 * n + 1) - a (2 * n)) (a (2 * n))` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Combine the linear equalities and inequalities to obtain the conclusion.
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
Introduce `a ⟨C, hC⟩ hh hs`. Rewrite using `[Metric.tendsto_atTop]`. Introduce `ε hε`. Establish `hC0 : 0 ≤ C` using `(abs_nonneg _).trans (hC 0)`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k : ℕ, C / 2 ^ k < ε / 2 := by`.

Establish `ht : Tendsto (fun k : ℕ ↦ C / 2 ^ k) atTop (𝓝 0)`. Simplify `(tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num)).const_mul C` using `[div_eq_mul_inv, ← inv_pow]`. Conclude with `(ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))).exists`. Take `⟨N, hN⟩` from `Halving.eventually_le a C hC hh hs k (ε / 4) (by positivity)`. Use `⟨N, fun n hn ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[Real.dist_eq, sub_zero]`. Combine the linear relations using `[hN n hn]`.
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
