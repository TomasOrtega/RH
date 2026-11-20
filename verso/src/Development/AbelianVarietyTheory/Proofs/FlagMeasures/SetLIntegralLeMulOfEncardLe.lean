import Mathlib

open MeasureTheory

namespace GlobalTheory.IndicatorSumEncard

/- English proof (translation)
Rewrite using `[← tsum_subtype A (fun _ => (1 : ENNReal))]`. Conclude with `ENNReal.tsum_set_one A`.
-/
theorem tsum_indicator_one_eq_encard {ι : Type} (A : Set ι) :
    ∑' i : ι, A.indicator (fun _ => (1 : ENNReal)) i = (A.encard : ENNReal) := by
  rw [← tsum_subtype A (fun _ => (1 : ENNReal))]
  exact ENNReal.tsum_set_one A

/- English proof (translation)
Establish `key : ∀ x : G, ∑' γ : ↥Γ, S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x) ≤ N`. Introduce `x`. Rewrite using `[← (Equiv.inv ↥Γ).tsum_eq (fun γ => S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x))]`. Simplify using `only [Equiv.inv_apply, inv_inv]`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Use `_ = _ := tsum_indicator_one_eq_encard _`. Use `_ ≤ N := hcount x`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← lintegral_indicator hS]`.

Conclude with `hD.lintegral_eq_tsum' _`. Use `_ = ∑' γ : ↥Γ, ∫⁻ x in D, S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x) * f x ∂μ := by`. Use `congr 1`. Use extensionality with `γ`. Use `lintegral_congr_ae ((ae_restrict_of_ae hinv).mono fun x hx => ?_)` and prove the remaining obligations.

Establish `h1 : f (γ⁻¹ • x) = f x` using `hx γ⁻¹`. Simplify using `only`. Distinguish the cases in `hm : γ⁻¹ • x ∈ S`. Rewrite using `[Set.indicator_of_mem hm, Set.indicator_of_mem hm, one_mul, h1]`. Rewrite using `[Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, zero_mul]`.

Use `_ = ∫⁻ x in D, (∑' γ : ↥Γ, S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x)) * f x ∂μ := by`. Rewrite using `[← lintegral_tsum]`. Use `congr 1`. Use extensionality with `x`. Rewrite using `[ENNReal.tsum_mul_right]`.

Introduce `γ`. Conclude with `(((measurable_const.indicator hS).comp (measurable_const_smul γ⁻¹)).aemeasurable).mul hf.restrict`. Use `_ ≤ ∫⁻ x in D, N * f x ∂μ := lintegral_mono fun x => by gcongr; exact key x`. Use `_ = N * ∫⁻ x in D, f x ∂μ := lintegral_const_mul' N _ hN`.
-/
theorem setLIntegral_le_mul_of_encard_le {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
    [Measure.IsMulLeftInvariant μ] {Γ : Subgroup G} [Countable ↥Γ] {D : Set G}
    (hD : IsFundamentalDomain (↥Γ) D μ) {f : G → ENNReal} (hf : AEMeasurable f μ)
    (hinv : ∀ᵐ (y : G) ∂μ, ∀ (γ : ↥Γ), f ((↑γ : G) * y) = f y) {S : Set G}
    (hS : MeasurableSet S) (N : ENNReal) (hN : N ≠ ⊤)
    (hcount : ∀ (z : G), (↑(Set.encard {γ : ↥Γ | (↑γ : G) * z ∈ S}) : ENNReal) ≤ N) :
    ∫⁻ (y : G) in S, f y ∂μ ≤ N * ∫⁻ (y : G) in D, f y ∂μ := by

  have key : ∀ x : G, ∑' γ : ↥Γ, S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x) ≤ N := by
    intro x
    rw [← (Equiv.inv ↥Γ).tsum_eq (fun γ => S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x))]
    simp only [Equiv.inv_apply, inv_inv]
    calc ∑' γ : ↥Γ, S.indicator (fun _ => (1 : ENNReal)) (γ • x)
        = ∑' γ : ↥Γ, {γ : ↥Γ | (↑γ : G) * x ∈ S}.indicator (fun _ => (1 : ENNReal)) γ := by
          congr 1
      _ = _ := tsum_indicator_one_eq_encard _
      _ ≤ N := hcount x

  calc ∫⁻ y in S, f y ∂μ = ∑' γ : ↥Γ, ∫⁻ x in D, S.indicator f (γ⁻¹ • x) ∂μ := by
        rw [← lintegral_indicator hS]
        exact hD.lintegral_eq_tsum' _
    _ = ∑' γ : ↥Γ, ∫⁻ x in D, S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x) * f x ∂μ := by
        congr 1
        ext γ
        refine lintegral_congr_ae ((ae_restrict_of_ae hinv).mono fun x hx => ?_)
        have h1 : f (γ⁻¹ • x) = f x := hx γ⁻¹
        dsimp only
        by_cases hm : γ⁻¹ • x ∈ S
        · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, one_mul, h1]
        · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, zero_mul]
    _ = ∫⁻ x in D, (∑' γ : ↥Γ, S.indicator (fun _ => (1 : ENNReal)) (γ⁻¹ • x)) * f x ∂μ := by
        rw [← lintegral_tsum]
        · congr 1
          ext x
          rw [ENNReal.tsum_mul_right]
        · intro γ
          exact (((measurable_const.indicator hS).comp (measurable_const_smul γ⁻¹)).aemeasurable).mul
            hf.restrict
    _ ≤ ∫⁻ x in D, N * f x ∂μ := lintegral_mono fun x => by gcongr; exact key x
    _ = N * ∫⁻ x in D, f x ∂μ := lintegral_const_mul' N _ hN

end GlobalTheory.IndicatorSumEncard
