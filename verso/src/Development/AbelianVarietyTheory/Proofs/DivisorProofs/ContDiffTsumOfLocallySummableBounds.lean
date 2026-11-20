import Mathlib

open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Use `choose u hus hub using hu`. Establish `hinf : ((⊤ : ℕ∞) : WithTop ℕ∞) = ∞` using `rfl`. Rewrite `hf`, the goal using `[hinf]`. Rewrite using `[contDiff_infty]`. Introduce `n`.

Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `t₀`. Set `ρ : ContDiffBump t₀` to `⟨1/2, 1, by norm_num, by norm_num⟩`. Use `set R : ℝ := ‖t₀‖ + 1 with hR`. Set `ρc : (Fin k → ℝ) → ℂ` to `fun t => ((ρ t : ℝ) : ℂ)`.

Establish `hρc : ContDiff ℝ ∞ ρc` using `Complex.ofRealCLM.contDiff.comp ρ.contDiff`. Establish `hρcs : HasCompactSupport ρc` using `ρ.hasCompactSupport.comp_left Complex.ofReal_zero`. Establish `hB : ∀ j : ℕ, ∃ B, ∀ x, ‖iteratedFDeriv ℝ j ρc x‖ ≤ B` using `fun j => (hρc.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support (hρcs.iteratedFDeriv j)`. Use `choose B hB using hB`. Establish `hsupp : ∀ j x, x ∉ Metric.closedBall t₀ 1 → iteratedFDeriv ℝ j ρc x = 0`.

Introduce `j x hx`. Assume the negation of the conclusion as `h`. Establish `hx1 : x ∈ tsupport ρc` using `support_iteratedFDeriv_subset j h`. Establish `h2 : tsupport ρc ⊆ tsupport (ρ : (Fin k → ℝ) → ℝ)` using `tsupport_comp_subset Complex.ofReal_zero _`. Rewrite `h2` using `[ρ.tsupport_eq]`.

Conclude with `hx (h2 hx1)`. Establish `hunonneg : ∀ m i, 0 ≤ u m R i` using `fun m i => (norm_nonneg _).trans (hub m R i 0 (by rw [norm_zero, hR]; positivity))`. Establish `hB0 : ∀ j, 0 ≤ B j` using `fun j => (norm_nonneg _).trans (hB j 0)`. Set `v : ℕ → ι → ℝ` to `fun m i => ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * B j * u (m - j) R i`. Establish `hv : ∀ m, Summable (v m)` using `fun m => by`.

Apply `summable_sum` to reduce the goal to its premises. Introduce `j _`. Conclude with `(hus (m - j) R).mul_left _`. Establish `hbound : ∀ m i x, ‖iteratedFDeriv ℝ m (fun y => ρc y * f i y) x‖ ≤ v m i`. Introduce `m i x`.

Use `(norm_iteratedFDeriv_mul_le hρc (hf i) x (by exact_mod_cast le_top)).trans ?_` and prove the remaining obligations. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `j _`. Distinguish the cases in `hx : x ∈ Metric.closedBall t₀ 1`. Establish `hxR : ‖x‖ ≤ R`.

Rewrite `hx` using `[Metric.mem_closedBall, dist_eq_norm]`. Use `norm_sub_norm_le x t₀` as an intermediate fact. Rewrite using `[hR]`. Combine the linear equalities and inequalities to obtain the conclusion. Apply `mul_le_mul _ (hub _ _ _ _ hxR) (norm_nonneg _) (mul_nonneg (by positivity) (hB0 j))` to reduce the goal to its premises.

Conclude with `mul_le_mul_of_nonneg_left (hB j x) (by positivity)`. Rewrite using `[hsupp j x hx, norm_zero, mul_zero, zero_mul]`. Conclude with `mul_nonneg (mul_nonneg (by positivity) (hB0 j)) (hunonneg _ _)`. Establish `hsm : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, ρc t * f i t)` using `contDiff_tsum (fun i => (hρc.mul (hf i)).of_le (by exact_mod_cast le_top)) (fun m _ => hv m) (fun m i x _ => hbound m i x)`. Establish `heq : (fun t => ∑' i, f i t) =ᶠ[nhds t₀] (fun t => ∑' i, ρc t * f i t)` using `by filter_upwards [Metric.closedBall_mem_nhds t₀ (by norm_num : (0:ℝ) < 1/2)] with t ht`.

Rewrite using `[tsum_mul_left]`. Establish `h1 : ρ t = 1` using `ρ.one_of_mem_closedBall ht`. Simplify using `[ρc, h1]`. Conclude with `(hsm.contDiffAt).congr_of_eventuallyEq heq`.
-/
theorem contDiff_tsum_of_locally_summable_bounds {k : ℕ} {ι : Type} (f : ι → (Fin k → ℝ) → ℂ)
    (hf : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i))
    (hu : ∀ (n : ℕ) (R : ℝ), ∃ u : ι → ℝ, Summable u ∧
      ∀ i t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (f i) t‖ ≤ u i) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, f i t) := by
  choose u hus hub using hu
  have hinf : ((⊤ : ℕ∞) : WithTop ℕ∞) = ∞ := rfl
  rw [hinf] at hf ⊢
  rw [contDiff_infty]
  intro n
  rw [contDiff_iff_contDiffAt]
  intro t₀
  let ρ : ContDiffBump t₀ := ⟨1/2, 1, by norm_num, by norm_num⟩
  set R : ℝ := ‖t₀‖ + 1 with hR
  let ρc : (Fin k → ℝ) → ℂ := fun t => ((ρ t : ℝ) : ℂ)
  have hρc : ContDiff ℝ ∞ ρc := Complex.ofRealCLM.contDiff.comp ρ.contDiff
  have hρcs : HasCompactSupport ρc := ρ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hB : ∀ j : ℕ, ∃ B, ∀ x, ‖iteratedFDeriv ℝ j ρc x‖ ≤ B := fun j =>
    (hρc.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hρcs.iteratedFDeriv j)
  choose B hB using hB
  have hsupp : ∀ j x, x ∉ Metric.closedBall t₀ 1 → iteratedFDeriv ℝ j ρc x = 0 := by
    intro j x hx
    by_contra h
    have hx1 : x ∈ tsupport ρc := support_iteratedFDeriv_subset j h
    have h2 : tsupport ρc ⊆ tsupport (ρ : (Fin k → ℝ) → ℝ) :=
      tsupport_comp_subset Complex.ofReal_zero _
    rw [ρ.tsupport_eq] at h2
    exact hx (h2 hx1)
  have hunonneg : ∀ m i, 0 ≤ u m R i := fun m i =>
    (norm_nonneg _).trans (hub m R i 0 (by rw [norm_zero, hR]; positivity))
  have hB0 : ∀ j, 0 ≤ B j := fun j => (norm_nonneg _).trans (hB j 0)
  let v : ℕ → ι → ℝ := fun m i =>
    ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * B j * u (m - j) R i
  have hv : ∀ m, Summable (v m) := fun m => by
    apply summable_sum
    intro j _
    exact (hus (m - j) R).mul_left _
  have hbound : ∀ m i x, ‖iteratedFDeriv ℝ m (fun y => ρc y * f i y) x‖ ≤ v m i := by
    intro m i x
    refine (norm_iteratedFDeriv_mul_le hρc (hf i) x (by exact_mod_cast le_top)).trans ?_
    apply Finset.sum_le_sum
    intro j _
    by_cases hx : x ∈ Metric.closedBall t₀ 1
    · have hxR : ‖x‖ ≤ R := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hx
        have := norm_sub_norm_le x t₀
        rw [hR]; linarith
      apply mul_le_mul _ (hub _ _ _ _ hxR) (norm_nonneg _)
        (mul_nonneg (by positivity) (hB0 j))
      exact mul_le_mul_of_nonneg_left (hB j x) (by positivity)
    · rw [hsupp j x hx, norm_zero, mul_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (by positivity) (hB0 j)) (hunonneg _ _)
  have hsm : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, ρc t * f i t) :=
    contDiff_tsum (fun i => (hρc.mul (hf i)).of_le (by exact_mod_cast le_top))
      (fun m _ => hv m) (fun m i x _ => hbound m i x)
  have heq : (fun t => ∑' i, f i t) =ᶠ[nhds t₀] (fun t => ∑' i, ρc t * f i t) := by
    filter_upwards [Metric.closedBall_mem_nhds t₀ (by norm_num : (0:ℝ) < 1/2)] with t ht
    rw [tsum_mul_left]
    have h1 : ρ t = 1 := ρ.one_of_mem_closedBall ht
    simp [ρc, h1]
  exact (hsm.contDiffAt).congr_of_eventuallyEq heq

end GlobalTheory
