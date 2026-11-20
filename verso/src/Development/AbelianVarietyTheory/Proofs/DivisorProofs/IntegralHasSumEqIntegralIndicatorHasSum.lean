import Mathlib
open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `X ι _ _ μ k hk hfin p K Kp hK hKp h0`. Use `set s := hfin.toFinset with hs`. Establish `hnull : ∀ i ∉ s, k i =ᵐ[μ] 0`. Introduce `i hi`. Establish `hi' : ∫ x, ‖k i x‖ ∂μ = 0`.

Assume the negation of the conclusion as `h`. Conclude with `hi (by simpa [hs] using h)`. Use `(integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg (k i x)) (hk i).norm).1 hi'` as an intermediate fact. Use `filter_upwards [this] with x hx`. Simplify using `using hx`.

Establish `hall : ∀ᵐ x ∂μ, ∀ i, i ∉ s → k i x = 0`. Rewrite using `[ae_all_iff]`. Introduce `i`. Distinguish the cases in `hi : i ∈ s`. Conclude with `Filter.Eventually.of_forall (fun x h => absurd hi h)`.

Use `filter_upwards [hnull i hi] with x hx _`. Conclude with `hx`. Establish `hKae : K =ᵐ[μ] fun x => ∑ i ∈ s, k i x` using `by filter_upwards [hall] with x hx`. Conclude with `(hK x).unique (hasSum_sum_of_ne_finset_zero (fun i hi => hx i hi))`. Establish `hKpae : Kp =ᵐ[μ] fun x => ∑ i ∈ s, p.indicator (fun i => k i x) i` using `by filter_upwards [hall] with x hx`.

Use `(hKp x).unique (hasSum_sum_of_ne_finset_zero (fun i hi => ?_))` and prove the remaining obligations. Distinguish the cases in `hp : i ∈ p`. Simplify using `[Set.indicator_of_mem hp, hx i hi]`. Simplify using `[Set.indicator_of_notMem hp]`. Establish `hind : ∀ i, (fun x => p.indicator (fun i => k i x) i) = if i ∈ p then k i else fun _ => 0`.

Introduce `i`. Distinguish the cases in `hp : i ∈ p`. Use function extensionality and compare the values at `x`. Simplify using `[Set.indicator_of_mem hp, hp]`. Use function extensionality and compare the values at `x`.

Simplify using `[Set.indicator_of_notMem hp, hp]`. Rewrite using `[integral_congr_ae hKae, integral_congr_ae hKpae, integral_finset_sum s (fun i _ => hk i), integral_finset_sum s (fun i _ => by`. Rewrite using `[hind i]`. Use `split_ifs`. Conclude with `hk i`.

Conclude with `integrable_zero _ _ _)]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[hind i]`. Use `split_ifs with hp`. Both sides reduce to the same expression.

Simplify using `[h0 i hp]`.
-/
theorem integral_hasSum_eq_integral_indicator_hasSum :
    ∀ {X ι : Type} [MeasurableSpace X] [Countable ι] (μ : Measure X) (k : ι → X → ℂ),
      (∀ i, Integrable (k i) μ) → {i | ∫ x, ‖k i x‖ ∂μ ≠ 0}.Finite →
      ∀ (p : Set ι) (K Kp : X → ℂ), (∀ x, HasSum (fun i => k i x) (K x)) →
      (∀ x, HasSum (fun i => p.indicator (fun i => k i x) i) (Kp x)) →
      (∀ i ∉ p, ∫ x, k i x ∂μ = 0) → ∫ x, K x ∂μ = ∫ x, Kp x ∂μ := by
  intro X ι _ _ μ k hk hfin p K Kp hK hKp h0
  classical
  set s := hfin.toFinset with hs
  have hnull : ∀ i ∉ s, k i =ᵐ[μ] 0 := by
    intro i hi
    have hi' : ∫ x, ‖k i x‖ ∂μ = 0 := by
      by_contra h
      exact hi (by simpa [hs] using h)
    have := (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg (k i x)) (hk i).norm).1 hi'
    filter_upwards [this] with x hx
    simpa using hx
  have hall : ∀ᵐ x ∂μ, ∀ i, i ∉ s → k i x = 0 := by
    rw [ae_all_iff]
    intro i
    by_cases hi : i ∈ s
    · exact Filter.Eventually.of_forall (fun x h => absurd hi h)
    · filter_upwards [hnull i hi] with x hx _
      exact hx
  have hKae : K =ᵐ[μ] fun x => ∑ i ∈ s, k i x := by
    filter_upwards [hall] with x hx
    exact (hK x).unique (hasSum_sum_of_ne_finset_zero (fun i hi => hx i hi))
  have hKpae : Kp =ᵐ[μ] fun x => ∑ i ∈ s, p.indicator (fun i => k i x) i := by
    filter_upwards [hall] with x hx
    refine (hKp x).unique (hasSum_sum_of_ne_finset_zero (fun i hi => ?_))
    by_cases hp : i ∈ p
    · simp [Set.indicator_of_mem hp, hx i hi]
    · simp [Set.indicator_of_notMem hp]
  have hind : ∀ i, (fun x => p.indicator (fun i => k i x) i) =
      if i ∈ p then k i else fun _ => 0 := by
    intro i
    by_cases hp : i ∈ p
    · funext x; simp [Set.indicator_of_mem hp, hp]
    · funext x; simp [Set.indicator_of_notMem hp, hp]
  rw [integral_congr_ae hKae, integral_congr_ae hKpae,
    integral_finset_sum s (fun i _ => hk i),
    integral_finset_sum s (fun i _ => by
      rw [hind i]; split_ifs
      · exact hk i
      · exact integrable_zero _ _ _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hind i]
  split_ifs with hp
  · rfl
  · simp [h0 i hp]

end GlobalTheory
