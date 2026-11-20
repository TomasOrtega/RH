import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IterDifferentiableOn
open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalLog

/- English proof (translation)
Introduce `B V _ _ _ _ b₀ h μ L ρ C _hρ hC hcontr happrox hhom hlim b hb s hs t ht hm`. Establish `hsk` using `fun k => iter_mem_ball b₀ h ρ hcontr hb hs k`. Establish `htk` using `fun k => iter_mem_ball b₀ h ρ hcontr hb ht k`. Establish `hiter : ∀ k : ℕ, iter h k (b, μ (b, s, t)) = μ (b, iter h k (b, s), iter h k (b, t))`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => rw [iter_zero, iter_zero, iter_zero]`. Consider the case `succ k ih`. Rewrite using `[iter_succ, iter_succ, iter_succ, ih]`. Conclude with `hhom b hb _ (hsk k) _ (htk k)`.

Establish `hn2 : ‖(2 : ℂ)‖ = 2` using `by simp`. Establish `herr : Tendsto (fun k : ℕ => (2 : ℂ) ^ k • (μ (b, iter h k (b, s), iter h k (b, t)) - iter h k (b, s) - iter h k (b, t))) atTop (𝓝 0)`. Establish `hg : Tendsto (fun k : ℕ => C * ‖s‖ * ‖t‖ * (18 / 25 : ℝ) ^ k) atTop (𝓝 0)`. Use `tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 18 / 25) (by norm_num : (18 / 25 : ℝ) < 1)` as an intermediate fact. Simplify using `using this.const_mul (C * ‖s‖ * ‖t‖)`.

Use `squeeze_zero_norm (fun k => ?_) hg` and prove the remaining obligations. Rewrite using `[norm_smul, norm_pow, hn2]`. Establish `h1` using `happrox b hb _ (hsk k) _ (htk k)`. Establish `h2` using `norm_iter_le b₀ h ρ hcontr hb hs k`. Establish `h3` using `norm_iter_le b₀ h ρ hcontr hb ht k`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Conclude with `mul_le_mul (mul_le_mul_of_nonneg_left h2 hC) h3 (norm_nonneg _) (mul_nonneg hC (by positivity))`. Use `_ = C * ‖s‖ * ‖t‖ * (18 / 25) ^ k := by`. Rewrite using `[show (18 / 25 : ℝ) = 2 * (3 / 5) * (3 / 5) by norm_num, mul_pow, mul_pow]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsum : Tendsto (fun k : ℕ => (2 : ℂ) ^ k • iter h k (b, μ (b, s, t))) atTop (𝓝 (L (b, s) + L (b, t) + 0))`. Use `(((hlim b hb s hs).add (hlim b hb t ht)).add herr).congr (fun k => ?_)` and prove the remaining obligations. Rewrite using `[hiter k, smul_sub, smul_sub]`. Normalize the expressions using the abelian group laws.

Rewrite `hsum` using `[add_zero]`. Conclude with `tendsto_nhds_unique (hlim b hb _ hm) hsum`.
-/
theorem koenigs_limit_additive_for_law : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] (b₀ : B) (h : B × V → V) (μ : B × V × V → V) (L : B × V → V) (ρ C : ℝ), 0 < ρ → 0 ≤ C → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, ‖μ (b, s, t) - s - t‖ ≤ C * ‖s‖ * ‖t‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, h (b, μ (b, s, t)) = μ (b, h (b, s), h (b, t))) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, Tendsto (fun k : ℕ => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k (b, s)) atTop (𝓝 (L (b, s)))) → ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ∀ t ∈ ball (0 : V) ρ, μ (b, s, t) ∈ ball (0 : V) ρ → L (b, μ (b, s, t)) = L (b, s) + L (b, t) := by
  intro B V _ _ _ _ b₀ h μ L ρ C _hρ hC hcontr happrox hhom hlim b hb s hs t ht hm
  have hsk := fun k => iter_mem_ball b₀ h ρ hcontr hb hs k
  have htk := fun k => iter_mem_ball b₀ h ρ hcontr hb ht k
  have hiter : ∀ k : ℕ, iter h k (b, μ (b, s, t)) = μ (b, iter h k (b, s), iter h k (b, t)) := by
    intro k
    induction k with
    | zero => rw [iter_zero, iter_zero, iter_zero]
    | succ k ih =>
      rw [iter_succ, iter_succ, iter_succ, ih]
      exact hhom b hb _ (hsk k) _ (htk k)
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  have herr : Tendsto (fun k : ℕ => (2 : ℂ) ^ k •
      (μ (b, iter h k (b, s), iter h k (b, t)) - iter h k (b, s) - iter h k (b, t))) atTop (𝓝 0) := by
    have hg : Tendsto (fun k : ℕ => C * ‖s‖ * ‖t‖ * (18 / 25 : ℝ) ^ k) atTop (𝓝 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 18 / 25)
        (by norm_num : (18 / 25 : ℝ) < 1)
      simpa using this.const_mul (C * ‖s‖ * ‖t‖)
    refine squeeze_zero_norm (fun k => ?_) hg
    rw [norm_smul, norm_pow, hn2]
    have h1 := happrox b hb _ (hsk k) _ (htk k)
    have h2 := norm_iter_le b₀ h ρ hcontr hb hs k
    have h3 := norm_iter_le b₀ h ρ hcontr hb ht k
    calc (2 : ℝ) ^ k * ‖μ (b, iter h k (b, s), iter h k (b, t)) - iter h k (b, s) - iter h k (b, t)‖
        ≤ 2 ^ k * (C * ‖iter h k (b, s)‖ * ‖iter h k (b, t)‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 ^ k * (C * ((3 / 5) ^ k * ‖s‖) * ((3 / 5) ^ k * ‖t‖)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hC) h3 (norm_nonneg _)
            (mul_nonneg hC (by positivity))
      _ = C * ‖s‖ * ‖t‖ * (18 / 25) ^ k := by
          rw [show (18 / 25 : ℝ) = 2 * (3 / 5) * (3 / 5) by norm_num, mul_pow, mul_pow]
          ring
  have hsum : Tendsto (fun k : ℕ => (2 : ℂ) ^ k • iter h k (b, μ (b, s, t))) atTop
      (𝓝 (L (b, s) + L (b, t) + 0)) := by
    refine (((hlim b hb s hs).add (hlim b hb t ht)).add herr).congr (fun k => ?_)
    rw [hiter k, smul_sub, smul_sub]
    abel
  rw [add_zero] at hsum
  exact tendsto_nhds_unique (hlim b hb _ hm) hsum

end GlobalTheory.CompanionTheory.Ar.Flat.LocalLog
