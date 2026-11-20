import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology

namespace GlobalTheory.KSp.FourMem

/- English proof (translation)
Establish `h1 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + t) = f x`. Use `IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_` and prove the remaining obligations. Establish `h2 : IsLocallyConstant fun q : X × X => (f (q.2 + q.1), f q.2)` using `(hf.1.comp_continuous (by fun_prop)).prodMk (hf.1.comp_continuous continuous_snd)`. Use `filter_upwards [h2.eventually_eq (0, x)] with q hq`. Simplify using `only [Prod.mk.injEq, add_zero] at hq`.

Rewrite using `[hq.1, hq.2]`. Establish `h2 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + -t) = f x`. Establish `h3 : Filter.Tendsto (fun t : X => -t) (𝓝 0) (𝓝 0)`. Simplify using `using (continuous_neg (G := X)).tendsto 0`. Conclude with `h3.eventually h1`.

Use `filter_upwards [h1, h2] with t ht ht' x`. Distinguish the cases in `hx : x ∈ tsupport f`. Conclude with `ht x hx`. Distinguish the cases in `hx' : x + t ∈ tsupport f`. Rewrite using `[← ht' _ hx', add_neg_cancel_right]`.

Rewrite using `[image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']`.
-/
theorem eventually_invariant {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    {f : X → ℂ} (hf : f ∈ SB X) : ∀ᶠ t in 𝓝 (0 : X), ∀ x, f (x + t) = f x := by
  have h1 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + t) = f x := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2 fun x _ => ?_
    have h2 : IsLocallyConstant fun q : X × X => (f (q.2 + q.1), f q.2) :=
      (hf.1.comp_continuous (by fun_prop)).prodMk (hf.1.comp_continuous continuous_snd)
    filter_upwards [h2.eventually_eq (0, x)] with q hq
    simp only [Prod.mk.injEq, add_zero] at hq
    rw [hq.1, hq.2]
  have h2 : ∀ᶠ t in 𝓝 (0 : X), ∀ x ∈ tsupport f, f (x + -t) = f x := by
    have h3 : Filter.Tendsto (fun t : X => -t) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg (G := X)).tendsto 0
    exact h3.eventually h1
  filter_upwards [h1, h2] with t ht ht' x
  by_cases hx : x ∈ tsupport f
  · exact ht x hx
  by_cases hx' : x + t ∈ tsupport f
  · rw [← ht' _ hx', add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

/- English proof (translation)
Introduce `X _ _ _ _ h μ _ e he φ hφ`. Use `haveI := h.grp`. Use `haveI := h.t2`. Use `haveI := h.lc`. Use `haveI := h.sc`.

Take `⟨K, hK, hKm⟩` from `he.big _ (eventually_invariant hφ)`. Use `⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun y => ?_, HasCompactSupport.intro hK fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ᶠ z in 𝓝 y, ∀ x ∈ tsupport φ, e z x = e y x`. Use `IsCompact.eventually_forall_of_forall_eventually hφ.2 fun x _ => ?_` and prove the remaining obligations. Establish `h2 : IsLocallyConstant fun q : X × X => (e q.1 q.2, e y q.2)` using `he.lc.prodMk (he.lc.comp_continuous (continuous_const.prodMk continuous_snd))`.

Use `filter_upwards [h2.eventually_eq (y, x)] with q hq`. Simplify using `only [Prod.mk.injEq] at hq`. Rewrite using `[hq.1, hq.2]`. Use `filter_upwards [h1] with z hz`. Unfold `four`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x ∈ tsupport φ`. Rewrite using `[hz x hx]`. Simplify using `[image_eq_zero_of_notMem_tsupport hx]`.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht, hne⟩ : ∃ t, (∀ x, φ (x + t) = φ x) ∧ e t y ≠ 1 := by`. Assume the negation of the conclusion as `hne`. Conclude with `hy (hKm y fun t ht => by`. Assume the negation of the conclusion as `h4`. Conclude with `hne ⟨t, ht, h4⟩)`.

Establish `h1` using `integral_add_right_eq_self (μ := μ) (fun x => e y x * φ x) t`. Establish `h2 : ∀ x, e y (x + t) * φ (x + t) = e t y * (e y x * φ x)`. Introduce `x`. Rewrite using `[ht, he.symm y (x + t), he.add, he.symm x y]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [h2, integral_const_mul] at h1`. Use `(mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne)` and prove the remaining obligations. Unfold `four`. Rewrite using `[sub_mul, h1, one_mul, sub_self]`.
-/
theorem four_mem_SB : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ φ ∈ SB X, four μ e φ ∈ SB X := by
  intro X _ _ _ _ h μ _ e he φ hφ
  haveI := h.grp
  haveI := h.t2
  haveI := h.lc
  haveI := h.sc
  obtain ⟨K, hK, hKm⟩ := he.big _ (eventually_invariant hφ)
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun y => ?_, HasCompactSupport.intro hK fun y hy => ?_⟩
  · have h1 : ∀ᶠ z in 𝓝 y, ∀ x ∈ tsupport φ, e z x = e y x := by
      refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun x _ => ?_
      have h2 : IsLocallyConstant fun q : X × X => (e q.1 q.2, e y q.2) :=
        he.lc.prodMk (he.lc.comp_continuous (continuous_const.prodMk continuous_snd))
      filter_upwards [h2.eventually_eq (y, x)] with q hq
      simp only [Prod.mk.injEq] at hq
      rw [hq.1, hq.2]
    filter_upwards [h1] with z hz
    unfold four
    congr 1
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [hz x hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · obtain ⟨t, ht, hne⟩ : ∃ t, (∀ x, φ (x + t) = φ x) ∧ e t y ≠ 1 := by
      by_contra hne
      exact hy (hKm y fun t ht => by
        by_contra h4
        exact hne ⟨t, ht, h4⟩)
    have h1 := integral_add_right_eq_self (μ := μ) (fun x => e y x * φ x) t
    have h2 : ∀ x, e y (x + t) * φ (x + t) = e t y * (e y x * φ x) := by
      intro x
      rw [ht, he.symm y (x + t), he.add, he.symm x y]; ring
    simp only [h2, integral_const_mul] at h1
    refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne)
    unfold four
    rw [sub_mul, h1, one_mul, sub_self]

end GlobalTheory.KSp.FourMem
