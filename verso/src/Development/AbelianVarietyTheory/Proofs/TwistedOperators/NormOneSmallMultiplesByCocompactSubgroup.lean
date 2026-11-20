import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

open MeasureTheory MeasureTheory.Measure GlobalTheory.RegSS
open scoped NNReal ENNReal

namespace GlobalTheory.RegSS

/- English proof (translation)
Set `A : Λ → Set X` to `fun l => (fun x => (l : X) + x) ⁻¹' S ∩ C`. Establish `hAm : ∀ l, MeasurableSet (A l)` using `fun l => ((measurable_const_add (l : X)) hS).inter hCm`. Establish `hdisj : Pairwise (Function.onFun Disjoint A)`. Introduce `l m hlm`. Rewrite using `[Function.onFun, Set.disjoint_left]`.

Introduce and unpack `x ⟨hx, -⟩ ⟨hx', -⟩`. Apply `hlm` to reduce the goal to its premises. Use `h _ hx _ hx' (by simpa using Λ.sub_mem l.2 m.2)` as an intermediate fact. Conclude with `Subtype.ext (add_right_cancel this)`. Establish `hcov : S ⊆ ⋃ l : Λ, (fun x => -(l : X) + x) ⁻¹' A l`.

Introduce `x hx`. Take `⟨l, hl, hxl⟩` from `hC x`. Use `Set.mem_iUnion.2 ⟨⟨l, hl⟩, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hx`. Simplify `hxl` using `[neg_add_eq_sub]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem measure_le_of_sub_mem_imp_eq {X : Type} [AddCommGroup X] [MeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddLeftInvariant] (Λ : AddSubgroup X) [Countable Λ]
    (C S : Set X) (hCm : MeasurableSet C) (hC : ∀ x, ∃ l ∈ Λ, x - l ∈ C) (hS : MeasurableSet S)
    (h : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ Λ → x = y) : μ S ≤ μ C := by
  let A : Λ → Set X := fun l => (fun x => (l : X) + x) ⁻¹' S ∩ C
  have hAm : ∀ l, MeasurableSet (A l) := fun l =>
    ((measurable_const_add (l : X)) hS).inter hCm
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro l m hlm
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨hx, -⟩ ⟨hx', -⟩
    apply hlm
    have := h _ hx _ hx' (by simpa using Λ.sub_mem l.2 m.2)
    exact Subtype.ext (add_right_cancel this)
  have hcov : S ⊆ ⋃ l : Λ, (fun x => -(l : X) + x) ⁻¹' A l := by
    intro x hx
    obtain ⟨l, hl, hxl⟩ := hC x
    refine Set.mem_iUnion.2 ⟨⟨l, hl⟩, ?_, ?_⟩
    · simpa using hx
    · simpa [neg_add_eq_sub] using hxl
  calc μ S ≤ μ (⋃ l : Λ, (fun x => -(l : X) + x) ⁻¹' A l) := measure_mono hcov
    _ ≤ ∑' l : Λ, μ ((fun x => -(l : X) + x) ⁻¹' A l) := measure_iUnion_le _
    _ = ∑' l : Λ, μ (A l) := by simp_rw [measure_preimage_add]
    _ = μ (⋃ l, A l) := (measure_iUnion hdisj hAm).symm
    _ ≤ μ C := measure_mono (Set.iUnion_subset fun l => Set.inter_subset_right)

/- English proof (translation)
Set `T : X ≃ₜ+ X` to `{ toFun := τ, invFun := τ, left_inv := hττ, right_inv := hττ, map_add' := map_add τ, continuous_toFun := hτ, continuous_invFun := hτ }`. Set `M : X ≃ₜ+ X` to `{ toFun := fun x => u * x, invFun := fun x => τ u * x, left_inv := fun x => by simp only [← mul_assoc, mul_comm (τ u) u, hu, one_mul], right_inv := fun x => by simp only [← mul_assoc, hu, one_mul], map_add' := mul_add u, continuous_toFun := continuous_const_mul u, continuous_invF …`. Establish `h1 : T.trans T = ContinuousAddEquiv.refl X`. Use extensionality with `x`. Conclude with `hττ x`.

Establish `h2 : (T.trans M).trans (T.trans M) = ContinuousAddEquiv.refl X`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `u * τ (u * τ x) = x`. Rewrite using `[map_mul, hττ, ← mul_assoc, hu, one_mul]`. Establish `e1` using `congrArg addEquivAddHaarChar h1`.

Establish `e2` using `congrArg addEquivAddHaarChar h2`. Simplify using `only [addEquivAddHaarChar_trans, addEquivAddHaarChar_refl] at e1 e2`. Establish `e3 : addEquivAddHaarChar M * addEquivAddHaarChar M = 1`. Rewrite using `[← e2, mul_mul_mul_comm, e1, one_mul]`. Establish `e4 : addEquivAddHaarChar M = 1`.

Use `(pow_eq_one_iff_of_nonneg (a := addEquivAddHaarChar M) zero_le two_ne_zero).1 (by rw [sq, e3])` as an intermediate fact. Conclude with `this`. Use `addEquivAddHaarChar_smul_preimage μ (X := S) M` as an intermediate fact. Rewrite `this` using `[e4, one_smul]`. Conclude with `this`.
-/
theorem measure_preimage_mul_of_norm_one {X : Type} [CommRing X] [TopologicalSpace X]
    [IsTopologicalRing X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.IsAddHaarMeasure] [μ.Regular] (τ : X →+* X) (hτ : Continuous τ)
    (hττ : ∀ x, τ (τ x) = x) (u : X) (hu : u * τ u = 1) (S : Set X) :
    μ ((fun x => u * x) ⁻¹' S) = μ S := by
  let T : X ≃ₜ+ X :=
    { toFun := τ, invFun := τ, left_inv := hττ, right_inv := hττ, map_add' := map_add τ,
      continuous_toFun := hτ, continuous_invFun := hτ }
  let M : X ≃ₜ+ X :=
    { toFun := fun x => u * x, invFun := fun x => τ u * x,
      left_inv := fun x => by simp only [← mul_assoc, mul_comm (τ u) u, hu, one_mul],
      right_inv := fun x => by simp only [← mul_assoc, hu, one_mul],
      map_add' := mul_add u,
      continuous_toFun := continuous_const_mul u, continuous_invFun := continuous_const_mul _ }
  have h1 : T.trans T = ContinuousAddEquiv.refl X := by
    ext x; exact hττ x
  have h2 : (T.trans M).trans (T.trans M) = ContinuousAddEquiv.refl X := by
    ext x
    change u * τ (u * τ x) = x
    rw [map_mul, hττ, ← mul_assoc, hu, one_mul]
  have e1 := congrArg addEquivAddHaarChar h1
  have e2 := congrArg addEquivAddHaarChar h2
  simp only [addEquivAddHaarChar_trans, addEquivAddHaarChar_refl] at e1 e2
  have e3 : addEquivAddHaarChar M * addEquivAddHaarChar M = 1 := by
    rw [← e2, mul_mul_mul_comm, e1, one_mul]
  have e4 : addEquivAddHaarChar M = 1 := by
    have := (pow_eq_one_iff_of_nonneg (a := addEquivAddHaarChar M) zero_le two_ne_zero).1
      (by rw [sq, e3])
    exact this
  have := addEquivAddHaarChar_smul_preimage μ (X := S) M
  rw [e4, one_smul] at this
  exact this

/- English proof (translation)
Introduce `X _ _ _ _ _ _ _ τ hτ hττ Λ hΛ ⟨C, hCc, hC⟩`. Use `borelize X`. Set `μ : Measure X` to `addHaar`. Establish `huniv : μ Set.univ = ∞` using `measure_univ_of_isAddLeftInvariant μ`. Take `⟨K, -, hKc, hK⟩` from `isOpen_univ.exists_lt_isCompact (μ := μ) (r := μ C) (by rw [huniv]; exact hCc.measure_lt_top)`.

Use `⟨(fun p : X × X => p.1 - p.2) '' (K ×ˢ K), (hKc.prod hKc).image (by fun_prop), ?_⟩` and prove the remaining obligations. Introduce `u hu`. Assume the negation of the conclusion as `hcon`. Establish `hle` using `measure_le_of_sub_mem_imp_eq μ Λ C ((fun x => u * x) ⁻¹' K) hCc.measurableSet hC ((continuous_const_mul u).measurable hKc.measurableSet) (by`. Introduce `x hx y hy hxy`.

Assume the negation of the conclusion as `hne`. Conclude with `hcon ⟨x - y, hxy, sub_ne_zero.2 hne, (u * x, u * y), ⟨hx, hy⟩, (mul_sub u x y).symm⟩)`. Rewrite `hle` using `[measure_preimage_mul_of_norm_one μ τ hτ hττ u hu]`. Conclude with `absurd hK (not_lt.2 hle)`.
-/
theorem normOnePacking : NormOnePacking := by
  intro X _ _ _ _ _ _ _ τ hτ hττ Λ hΛ ⟨C, hCc, hC⟩
  borelize X
  let μ : Measure X := addHaar
  have huniv : μ Set.univ = ∞ := measure_univ_of_isAddLeftInvariant μ
  obtain ⟨K, -, hKc, hK⟩ := isOpen_univ.exists_lt_isCompact (μ := μ) (r := μ C)
    (by rw [huniv]; exact hCc.measure_lt_top)
  refine ⟨(fun p : X × X => p.1 - p.2) '' (K ×ˢ K), (hKc.prod hKc).image (by fun_prop), ?_⟩
  intro u hu
  by_contra hcon
  have hle := measure_le_of_sub_mem_imp_eq μ Λ C ((fun x => u * x) ⁻¹' K) hCc.measurableSet hC
    ((continuous_const_mul u).measurable hKc.measurableSet) (by
      intro x hx y hy hxy
      by_contra hne
      exact hcon ⟨x - y, hxy, sub_ne_zero.2 hne, (u * x, u * y), ⟨hx, hy⟩, (mul_sub u x y).symm⟩)
  rw [measure_preimage_mul_of_norm_one μ τ hτ hττ u hu] at hle
  exact absurd hK (not_lt.2 hle)

end GlobalTheory.RegSS
