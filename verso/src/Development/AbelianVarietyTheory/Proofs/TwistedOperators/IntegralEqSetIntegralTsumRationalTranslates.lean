import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.Periodize

/- English proof (translation)
Take `⟨i1, i2, i3, i4, i5, -⟩` from `GlobalTheory.MixModel.lattice_Mx D m n`. Use `haveI : BorelSpace (Mx D m n) := ⟨rfl⟩`. Use `haveI : DiscreteTopology (ratMx D m n) := i5`. Use `haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Set `e : Matrix (Fin m) (Fin n) D.host.E ≃ ratMx D m n` to `Equiv.ofBijective (fun a => ⟨a.map (incA D), a, rfl⟩) ⟨fun a b h => Matrix.map_injective GlobalTheory.MixModel.incA_injective (congrArg Subtype.val h), fun γ => by obtain ⟨a, ha⟩ := γ.2; exact ⟨a, Subtype.ext ha⟩⟩`.

Establish `he : ∀ a, ((e a : ratMx D m n) : Mx D m n) = a.map (incA D)` using `fun _ => rfl`. Establish `hm : ∀ γ : ratMx D m n, AEStronglyMeasurable (fun y => c (y + γ)) (μ.restrict 𝓕)`. Introduce `γ`. Use `hc.1.comp_quasiMeasurePreserving (measurePreserving_add_right μ (γ : Mx D m n)).quasiMeasurePreserving` as an intermediate fact. Conclude with `this.restrict`.

Establish `hl : ∑' γ : ratMx D m n, ∫⁻ y in 𝓕, ‖c (y + γ)‖ₑ ∂μ = ∫⁻ y, ‖c y‖ₑ ∂μ`. Rewrite using `[hF.lintegral_eq_tsum'' (fun y => ‖c y‖ₑ)]`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Simplify using `only [AddSubgroup.vadd_def, vadd_eq_add, add_comm (γ : Mx D m n)]`. Establish `hfin : ∑' γ : ratMx D m n, ∫⁻ y in 𝓕, ‖c (y + γ)‖ₑ ∂μ ≠ ⊤`.

Rewrite using `[hl]`. Conclude with `hc.2.ne`. Establish `hae : ∀ᵐ y ∂(μ.restrict 𝓕), Summable fun γ : ratMx D m n => ‖c (y + γ)‖`. Establish `h1 : ∫⁻ y in 𝓕, ∑' γ : ratMx D m n, ‖c (y + γ)‖ₑ ∂μ ≠ ⊤`. Rewrite using `[lintegral_tsum fun γ => (hm γ).enorm]`.

Conclude with `hfin`. Establish `h2 : AEMeasurable (fun y => ∑' γ : ratMx D m n, ‖c (y + γ)‖ₑ) (μ.restrict 𝓕)` using `AEMeasurable.ennreal_tsum fun γ => (hm γ).enorm`. Use `filter_upwards [ae_lt_top' h2 h1] with y hy`. Establish `: ∑' γ : ratMx D m n, (‖c (y + γ)‖₊ : ENNReal) ≠ ⊤`. Simplify `hy.ne` using `only [enorm_eq_nnnorm]`.

Conclude with `(NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 this)).congr fun _ => rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hae] with y hy`. Conclude with `(e.summable_iff.2 hy).congr fun a => by rw [Function.comp_apply, he]`. Establish `h3 : ∫ y in 𝓕, ∑' γ : ratMx D m n, c (y + γ) ∂μ = ∑' γ : ratMx D m n, ∫ y in 𝓕, c (y + γ) ∂μ` using `integral_tsum hm hfin`.

Establish `h4 : ∫ y, c y ∂μ = ∑' γ : ratMx D m n, ∫ y in 𝓕, c (y + γ) ∂μ`. Rewrite using `[hF.integral_eq_tsum' c hc, ← (Equiv.neg (ratMx D m n)).tsum_eq]`. Use `tsum_congr fun γ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add, add_comm (γ : Mx D m n)]`. Rewrite using `[h4, ← h3]`.

Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[← e.tsum_eq]`. Both sides reduce to the same expression.
-/
theorem integral_eq_setIntegral_tsum (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n))
    (hμ : μ.IsAddHaarMeasure) (hF : IsAddFundamentalDomain (ratMx D m n) 𝓕 μ) (c : Mx D m n → ℂ)
    (hc : Integrable c μ) :
    (∀ᵐ y ∂(μ.restrict 𝓕), Summable fun a : Matrix (Fin m) (Fin n) D.host.E => ‖c (y + a.map (incA D))‖) ∧
      ∫ y, c y ∂μ = ∫ y in 𝓕, ∑' a : Matrix (Fin m) (Fin n) D.host.E, c (y + a.map (incA D)) ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : DiscreteTopology (ratMx D m n) := i5
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance

  let e : Matrix (Fin m) (Fin n) D.host.E ≃ ratMx D m n :=
    Equiv.ofBijective (fun a => ⟨a.map (incA D), a, rfl⟩)
      ⟨fun a b h => Matrix.map_injective GlobalTheory.MixModel.incA_injective (congrArg Subtype.val h),
        fun γ => by obtain ⟨a, ha⟩ := γ.2; exact ⟨a, Subtype.ext ha⟩⟩
  have he : ∀ a, ((e a : ratMx D m n) : Mx D m n) = a.map (incA D) := fun _ => rfl

  have hm : ∀ γ : ratMx D m n, AEStronglyMeasurable (fun y => c (y + γ)) (μ.restrict 𝓕) := by
    intro γ
    have := hc.1.comp_quasiMeasurePreserving (measurePreserving_add_right μ (γ : Mx D m n)).quasiMeasurePreserving
    exact this.restrict

  have hl : ∑' γ : ratMx D m n, ∫⁻ y in 𝓕, ‖c (y + γ)‖ₑ ∂μ = ∫⁻ y, ‖c y‖ₑ ∂μ := by
    rw [hF.lintegral_eq_tsum'' (fun y => ‖c y‖ₑ)]
    refine tsum_congr fun γ => ?_
    simp only [AddSubgroup.vadd_def, vadd_eq_add, add_comm (γ : Mx D m n)]
  have hfin : ∑' γ : ratMx D m n, ∫⁻ y in 𝓕, ‖c (y + γ)‖ₑ ∂μ ≠ ⊤ := by
    rw [hl]; exact hc.2.ne

  have hae : ∀ᵐ y ∂(μ.restrict 𝓕), Summable fun γ : ratMx D m n => ‖c (y + γ)‖ := by
    have h1 : ∫⁻ y in 𝓕, ∑' γ : ratMx D m n, ‖c (y + γ)‖ₑ ∂μ ≠ ⊤ := by
      rw [lintegral_tsum fun γ => (hm γ).enorm]; exact hfin
    have h2 : AEMeasurable (fun y => ∑' γ : ratMx D m n, ‖c (y + γ)‖ₑ) (μ.restrict 𝓕) :=
      AEMeasurable.ennreal_tsum fun γ => (hm γ).enorm
    filter_upwards [ae_lt_top' h2 h1] with y hy
    have : ∑' γ : ratMx D m n, (‖c (y + γ)‖₊ : ENNReal) ≠ ⊤ := by
      simpa only [enorm_eq_nnnorm] using hy.ne
    exact (NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 this)).congr fun _ => rfl
  refine ⟨?_, ?_⟩
  · filter_upwards [hae] with y hy
    exact (e.summable_iff.2 hy).congr fun a => by rw [Function.comp_apply, he]
  · have h3 : ∫ y in 𝓕, ∑' γ : ratMx D m n, c (y + γ) ∂μ = ∑' γ : ratMx D m n, ∫ y in 𝓕, c (y + γ) ∂μ :=
      integral_tsum hm hfin
    have h4 : ∫ y, c y ∂μ = ∑' γ : ratMx D m n, ∫ y in 𝓕, c (y + γ) ∂μ := by
      rw [hF.integral_eq_tsum' c hc, ← (Equiv.neg (ratMx D m n)).tsum_eq]
      refine tsum_congr fun γ => ?_
      simp only [Equiv.neg_apply, neg_neg, AddSubgroup.vadd_def, vadd_eq_add, add_comm (γ : Mx D m n)]
    rw [h4, ← h3]
    congr 1
    funext y
    rw [← e.tsum_eq]
    rfl

end GlobalTheory.Twist.Periodize
