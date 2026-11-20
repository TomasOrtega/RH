import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

/- English proof (translation)
Simplify using `only [primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp`. Conclude with `⟨(Nat.floor_lt hx).mp hp.1.1, (Nat.le_floor_iff (hx.trans hxy)).mp hp.1.2⟩`.
-/
theorem mem_primesIoc_bounds {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) {p : ℕ} (hp : p ∈ primesIoc x y) :
    x < p ∧ (p : ℝ) ≤ y := by
  simp only [primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
  exact ⟨(Nat.floor_lt hx).mp hp.1.1, (Nat.le_floor_iff (hx.trans hxy)).mp hp.1.2⟩

/- English proof (translation)
Establish `hs : primesIoc x t = (primesIoc x y).filter (fun p : ℕ => (p : ℝ) ≤ t)`. Use extensionality with `p`. Simplify using `only [primesIoc, Finset.mem_filter, Finset.mem_Ioc]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, hp⟩`.

Conclude with `⟨⟨⟨h1, h2.trans (Nat.floor_mono hty)⟩, hp⟩, (Nat.le_floor_iff ht).mp h2⟩`. Introduce and unpack `⟨⟨⟨h1, _⟩, hp⟩, h3⟩`. Conclude with `⟨⟨h1, (Nat.le_floor_iff ht).mpr h3⟩, hp⟩`. Rewrite using `[hs, Finset.sum_filter]`. Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations.

Apply the tactic sequence `by_cases h : (p : ℝ) ≤ t <;> simp [h]`.
-/
theorem sum_primesIoc_eq_sum_indicator (a : ℕ → ℂ) {x y t : ℝ} (ht : 0 ≤ t) (hty : t ≤ y) :
    ∑ p ∈ primesIoc x t, a p
      = ∑ p ∈ primesIoc x y, (Set.Ici (p : ℝ)).indicator (fun _ => a p) t := by
  have hs : primesIoc x t = (primesIoc x y).filter (fun p : ℕ => (p : ℝ) ≤ t) := by
    ext p
    simp only [primesIoc, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨⟨h1, h2.trans (Nat.floor_mono hty)⟩, hp⟩, (Nat.le_floor_iff ht).mp h2⟩
    · rintro ⟨⟨⟨h1, _⟩, hp⟩, h3⟩
      exact ⟨⟨h1, (Nat.le_floor_iff ht).mpr h3⟩, hp⟩
  rw [hs, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : (p : ℝ) ≤ t <;> simp [h]

/- English proof (translation)
Rewrite `hf`, the goal using `[intervalIntegrable_iff]`. Conclude with `hf.indicator measurableSet_Ici`.
-/
private lemma intervalIntegrable_indicator_Ici_of_intervalIntegrable {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {x y p : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume x y) :
    IntervalIntegrable ((Set.Ici p).indicator f) MeasureTheory.volume x y := by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.indicator measurableSet_Ici

/- English proof (translation)
Establish `hxy : x ≤ y` using `hxp.le.trans hpy`. Rewrite using `[intervalIntegral.integral_of_le hxy, MeasureTheory.setIntegral_indicator measurableSet_Ici]`. Establish `hset : Set.Ioc x y ∩ Set.Ici p = Set.Icc p y`. Use extensionality with `t`. Simplify using `only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨_, h2⟩, h3⟩`. Conclude with `⟨h3, h2⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨hxp.trans_le h1, h2⟩, h1⟩`.

Rewrite using `[hset, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpy]`. Establish `hsub : Set.uIcc p y ⊆ Set.Icc x y`. Rewrite using `[Set.uIcc_of_le hpy]`. Conclude with `Set.Icc_subset_Icc hxp.le le_rfl`. Establish `hc' : ContinuousOn (fun t => (J' t : ℂ)) (Set.Icc x y)` using `Complex.continuous_ofReal.comp_continuousOn hc`.

Conclude with `intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => (hJ t (hsub ht)).ofReal_comp) ((hc'.mono hsub).intervalIntegrable)`.
-/
private lemma integral_indicator_Ici_deriv_eq_sub_of_hasDerivAt {J J' : ℝ → ℝ} {x y p : ℝ} (hxp : x < p) (hpy : p ≤ y)
    (hJ : ∀ t ∈ Set.Icc x y, HasDerivAt J (J' t) t) (hc : ContinuousOn J' (Set.Icc x y)) :
    ∫ t in x..y, (Set.Ici p).indicator (fun t => (J' t : ℂ)) t = (J y : ℂ) - J p := by
  have hxy : x ≤ y := hxp.le.trans hpy
  rw [intervalIntegral.integral_of_le hxy, MeasureTheory.setIntegral_indicator measurableSet_Ici]
  have hset : Set.Ioc x y ∩ Set.Ici p = Set.Icc p y := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨hxp.trans_le h1, h2⟩, h1⟩
  rw [hset, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpy]
  have hsub : Set.uIcc p y ⊆ Set.Icc x y := by
    rw [Set.uIcc_of_le hpy]
    exact Set.Icc_subset_Icc hxp.le le_rfl
  have hc' : ContinuousOn (fun t => (J' t : ℂ)) (Set.Icc x y) :=
    Complex.continuous_ofReal.comp_continuousOn hc
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => (hJ t (hsub ht)).ofReal_comp)
    ((hc'.mono hsub).intervalIntegrable)

/- English proof (translation)
Establish `hx0 : (0 : ℝ) ≤ x` using `zero_le_one.trans hx`. Take `⟨S, hS⟩ : ∃ S : ℝ → ℂ, S = fun t => ∑ p ∈ primesIoc x y, (Set.Ici (p : ℝ)).indicator (fun _ => a p) t` from `⟨_, rfl⟩`. Establish `hIcc : Set.uIcc x y = Set.Icc x y` using `Set.uIcc_of_le hxy`. Establish `hc' : ContinuousOn (fun t => (J' t : ℂ)) (Set.Icc x y)` using `Complex.continuous_ofReal.comp_continuousOn hc`. Establish `hJi : IntervalIntegrable (fun t => (J' t : ℂ)) MeasureTheory.volume x y` using `(hc'.mono hIcc.subset).intervalIntegrable`.

Establish `hterm : ∀ p ∈ primesIoc x y, IntervalIntegrable (fun t => a p * (Set.Ici (p : ℝ)).indicator (fun t => (J' t : ℂ)) t) MeasureTheory.volume x y` using `fun p _ => (intervalIntegrable_indicator_Ici_of_intervalIntegrable hJi).const_mul (a p)`. Establish `hpt : ∀ t, (J' t : ℂ) * S t = ∑ p ∈ primesIoc x y, a p * (Set.Ici (p : ℝ)).indicator (fun t => (J' t : ℂ)) t`. Introduce `t`. Rewrite using `[hS, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations.

Distinguish the cases in `h : t ∈ Set.Ici (p : ℝ)`. Simplify using `only [Set.indicator_of_mem h]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Set.indicator_of_notMem h]`. Establish `hL : ∑ p ∈ primesIoc x y, a p * ((J p - J y : ℝ) : ℂ) = -∫ t in x..y, (J' t : ℂ) * S t`.

Repeatedly rewrite using `[hpt]`. Rewrite using `[intervalIntegral.integral_finsetSum hterm, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl (fun p hp => ?_)` and prove the remaining obligations. Establish `hb` using `mem_primesIoc_bounds hx0 hxy hp`. Rewrite using `[intervalIntegral.integral_const_mul, integral_indicator_Ici_deriv_eq_sub_of_hasDerivAt hb.1 hb.2 hJ hc]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hSi : IntervalIntegrable S MeasureTheory.volume x y`. Establish `hS' : S = ∑ p ∈ primesIoc x y, (Set.Ici (p : ℝ)).indicator (fun _ => a p)`. Rewrite using `[hS]`.

Use function extensionality and compare the values at `t`. Simplify using `[Finset.sum_apply]`. Rewrite using `[hS']`. Conclude with `IntervalIntegrable.sum _ (fun p _ => intervalIntegrable_indicator_Ici_of_intervalIntegrable intervalIntegrable_const)`. Establish `hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc x y)`.

Apply `ContinuousOn.inv₀ continuousOn_id` to reduce the goal to its premises. Introduce `t ht`. Rewrite `ht` using `[hIcc]`. Conclude with `(lt_of_lt_of_le zero_lt_one (hx.trans ht.1)).ne'`. Establish `hg : IntervalIntegrable (fun t => r * (‖S t‖ / t)) MeasureTheory.volume x y`.

Use `(hSi.norm.mul_continuousOn hinv).const_mul r` as an intermediate fact. Simplify `this` using `[div_eq_mul_inv]`. Establish `hf : IntervalIntegrable (fun t => ‖(J' t : ℂ) * S t‖) MeasureTheory.volume x y`. Establish `hsum` using `IntervalIntegrable.sum _ hterm`. Establish `he : (fun t => (J' t : ℂ) * S t) = ∑ p ∈ primesIoc x y, (fun t => a p * (Set.Ici (p : ℝ)).indicator (fun t => (J' t : ℂ)) t)`.

Use function extensionality and compare the values at `t`. Rewrite using `[hpt, Finset.sum_apply]`. Rewrite `hsum` using `[← he]`. Conclude with `hsum.norm`. Establish `hA : ∀ t ∈ Set.uIcc x y, ‖∑ p ∈ primesIoc x t, a p‖ / t = ‖S t‖ / t`.

Introduce `t ht`. Rewrite `ht` using `[hIcc]`. Rewrite using `[sum_primesIoc_eq_sum_indicator a (hx0.trans ht.1) ht.2, hS]`. Rewrite using `[hL, norm_neg, intervalIntegral.integral_congr hA, ← intervalIntegral.integral_const_mul]`. Use `(intervalIntegral.norm_integral_le_integral_norm hxy).trans ?_` and prove the remaining obligations.

Use `intervalIntegral.integral_mono_on hxy hf hg (fun t ht => ?_)` and prove the remaining obligations. Establish `ht0 : 0 < t` using `lt_of_lt_of_le zero_lt_one (hx.trans ht.1)`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem abel_primesIoc_weight (a : ℕ → ℂ) (J J' : ℝ → ℝ) (x y r : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y)
    (hJ : ∀ t ∈ Set.Icc x y, HasDerivAt J (J' t) t) (hc : ContinuousOn J' (Set.Icc x y))
    (hb : ∀ t ∈ Set.Icc x y, |J' t| ≤ r / t) :
    ‖∑ p ∈ primesIoc x y, a p * ((J p - J y : ℝ) : ℂ)‖
      ≤ r * ∫ t in x..y, ‖∑ p ∈ primesIoc x t, a p‖ / t := by
  have hx0 : (0 : ℝ) ≤ x := zero_le_one.trans hx
  obtain ⟨S, hS⟩ : ∃ S : ℝ → ℂ, S = fun t => ∑ p ∈ primesIoc x y, (Set.Ici (p : ℝ)).indicator (fun _ => a p) t :=
    ⟨_, rfl⟩
  have hIcc : Set.uIcc x y = Set.Icc x y := Set.uIcc_of_le hxy
  have hc' : ContinuousOn (fun t => (J' t : ℂ)) (Set.Icc x y) :=
    Complex.continuous_ofReal.comp_continuousOn hc
  have hJi : IntervalIntegrable (fun t => (J' t : ℂ)) MeasureTheory.volume x y :=
    (hc'.mono hIcc.subset).intervalIntegrable
  have hterm : ∀ p ∈ primesIoc x y, IntervalIntegrable
      (fun t => a p * (Set.Ici (p : ℝ)).indicator (fun t => (J' t : ℂ)) t) MeasureTheory.volume x y :=
    fun p _ => (intervalIntegrable_indicator_Ici_of_intervalIntegrable hJi).const_mul (a p)
  have hpt : ∀ t, (J' t : ℂ) * S t
      = ∑ p ∈ primesIoc x y, a p * (Set.Ici (p : ℝ)).indicator (fun t => (J' t : ℂ)) t := by
    intro t
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : t ∈ Set.Ici (p : ℝ)
    · simp only [Set.indicator_of_mem h]
      ring
    · simp [Set.indicator_of_notMem h]
  have hL : ∑ p ∈ primesIoc x y, a p * ((J p - J y : ℝ) : ℂ) = -∫ t in x..y, (J' t : ℂ) * S t := by
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum hterm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hb := mem_primesIoc_bounds hx0 hxy hp
    rw [intervalIntegral.integral_const_mul, integral_indicator_Ici_deriv_eq_sub_of_hasDerivAt hb.1 hb.2 hJ hc]
    push_cast
    ring
  have hSi : IntervalIntegrable S MeasureTheory.volume x y := by
    have hS' : S = ∑ p ∈ primesIoc x y, (Set.Ici (p : ℝ)).indicator (fun _ => a p) := by
      rw [hS]
      funext t
      simp [Finset.sum_apply]
    rw [hS']
    exact IntervalIntegrable.sum _ (fun p _ => intervalIntegrable_indicator_Ici_of_intervalIntegrable intervalIntegrable_const)
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc x y) := by
    apply ContinuousOn.inv₀ continuousOn_id
    intro t ht
    rw [hIcc] at ht
    exact (lt_of_lt_of_le zero_lt_one (hx.trans ht.1)).ne'
  have hg : IntervalIntegrable (fun t => r * (‖S t‖ / t)) MeasureTheory.volume x y := by
    have := (hSi.norm.mul_continuousOn hinv).const_mul r
    simpa [div_eq_mul_inv] using this
  have hf : IntervalIntegrable (fun t => ‖(J' t : ℂ) * S t‖) MeasureTheory.volume x y := by
    have hsum := IntervalIntegrable.sum _ hterm
    have he : (fun t => (J' t : ℂ) * S t)
        = ∑ p ∈ primesIoc x y, (fun t => a p * (Set.Ici (p : ℝ)).indicator (fun t => (J' t : ℂ)) t) := by
      funext t
      rw [hpt, Finset.sum_apply]
    rw [← he] at hsum
    exact hsum.norm
  have hA : ∀ t ∈ Set.uIcc x y, ‖∑ p ∈ primesIoc x t, a p‖ / t = ‖S t‖ / t := by
    intro t ht
    rw [hIcc] at ht
    rw [sum_primesIoc_eq_sum_indicator a (hx0.trans ht.1) ht.2, hS]
  rw [hL, norm_neg, intervalIntegral.integral_congr hA, ← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.norm_integral_le_integral_norm hxy).trans ?_
  refine intervalIntegral.integral_mono_on hxy hf hg (fun t ht => ?_)
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one (hx.trans ht.1)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |J' t| * ‖S t‖ ≤ r / t * ‖S t‖ := mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg _)
    _ = r * (‖S t‖ / t) := by ring

end GlobalTheory.Lin
