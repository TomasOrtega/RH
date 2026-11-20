import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrArchPairAdeleJoin

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
open MeasureTheory
namespace GlobalTheory.WeilL2Words

/- English proof (translation)
Introduce `F _ _ κ _ μ hμ D hD h0`. Use `letI : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _`. Use `haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩`. Use function extensionality and compare the values at `a`. Assume the negation of the conclusion as `ha`.

Use `set x0 := archPart F a`. Use `set y0 : κ → FiniteAdeleRing (𝓞 F) F := fun i => (a i).2`. Establish `ha0 : D (GlobalTheory.WeilCont.adeleJoin F x0 y0) ≠ 0`. Rewrite using `[adeleJoin_archPart]`. Conclude with `ha`.

Take `⟨n, f, g, hg, hDs⟩` from `schA_exists_sum F hD`. Take `⟨s, hs⟩` from `GlobalTheory.WeilCont.exists_slice F hD y0`. Use `set V : Set (κ → FiniteAdeleRing (𝓞 F) F) := {y | ∀ i, g i y = g i y0}`. Establish `hVo : IsOpen V`. Establish `: V = ⋂ i, {y | g i y = g i y0}` using `by ext y; simp [V]`.

Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun i => (hg i).1.isOpen_fiber _`. Establish `hV : ∀ y ∈ V, ∀ x, D (GlobalTheory.WeilCont.adeleJoin F x y) = s x`. Introduce `y hy x`. Rewrite using `[hs, hDs, Finset.sum_apply, Finset.sum_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.WeilCont.pureA_adeleJoin, GlobalTheory.WeilCont.pureA_adeleJoin, hy i]`. Establish `hsc : Continuous fun x => ‖s x‖ₑ ^ 2` using `(ENNReal.continuous_pow 2).comp (continuous_enorm.comp s.continuous)`. Use `haveI : BorelSpace (mixedEmbedding.mixedSpace F) := inferInstance`. Use `haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := inferInstance`.

Use `haveI h1 : (volume : Measure (mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := inferInstance`. Use `haveI h2 : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Establish `hc : (∫⁻ x, ‖s x‖ₑ ^ 2) ≠ 0`. Introduce `hc`. Establish `hae` using `(lintegral_eq_zero_iff' hsc.aemeasurable).1 hc`.

Establish `heq` using `(Continuous.ae_eq_iff_eq volume hsc continuous_const).1 hae`. Establish `: ‖s x0‖ₑ ^ 2 = 0` using `congrFun heq x0`. Rewrite `this` using `[pow_eq_zero_iff two_ne_zero, enorm_eq_zero, hs]`. Conclude with `ha0 this`. Establish `hμV : μ V ≠ 0` using `hVo.measure_ne_zero μ ⟨y0, fun i => rfl⟩`.

Establish `hle : (∫⁻ x, ‖s x‖ₑ ^ 2) * μ V ≤ l2A F μ D`. Rewrite using `[← lintegral_indicator_const hVo.measurableSet]`. Unfold `l2A`. Use `lintegral_mono fun y => ?_` and prove the remaining obligations. Distinguish the cases in `hy : y ∈ V`.

Rewrite using `[Set.indicator_of_mem hy]`. Conclude with `le_of_eq (lintegral_congr fun x => by rw [hV y hy x])`. Rewrite using `[Set.indicator_of_notMem hy]`. Conclude with `bot_le`. Rewrite `hle` using `[h0]`.

Conclude with `mul_ne_zero hc hμV (le_antisymm hle bot_le)`.
-/
theorem eq_zero_of_l2A_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ D ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.l2A F μ D = 0 → D = 0 := by
  intro F _ _ κ _ μ hμ D hD h0
  letI : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  funext a
  by_contra ha
  set x0 := archPart F a
  set y0 : κ → FiniteAdeleRing (𝓞 F) F := fun i => (a i).2
  have ha0 : D (GlobalTheory.WeilCont.adeleJoin F x0 y0) ≠ 0 := by
    rw [adeleJoin_archPart]; exact ha
  obtain ⟨n, f, g, hg, hDs⟩ := schA_exists_sum F hD
  obtain ⟨s, hs⟩ := GlobalTheory.WeilCont.exists_slice F hD y0
  set V : Set (κ → FiniteAdeleRing (𝓞 F) F) := {y | ∀ i, g i y = g i y0}
  have hVo : IsOpen V := by
    have : V = ⋂ i, {y | g i y = g i y0} := by ext y; simp [V]
    rw [this]
    exact isOpen_iInter_of_finite fun i => (hg i).1.isOpen_fiber _
  have hV : ∀ y ∈ V, ∀ x, D (GlobalTheory.WeilCont.adeleJoin F x y) = s x := by
    intro y hy x
    rw [hs, hDs, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.WeilCont.pureA_adeleJoin, GlobalTheory.WeilCont.pureA_adeleJoin, hy i]
  have hsc : Continuous fun x => ‖s x‖ₑ ^ 2 := (ENNReal.continuous_pow 2).comp (continuous_enorm.comp s.continuous)
  haveI : BorelSpace (mixedEmbedding.mixedSpace F) := inferInstance
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := inferInstance
  haveI h1 : (volume : Measure (mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := inferInstance
  haveI h2 : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hc : (∫⁻ x, ‖s x‖ₑ ^ 2) ≠ 0 := by
    intro hc
    have hae := (lintegral_eq_zero_iff' hsc.aemeasurable).1 hc
    have heq := (Continuous.ae_eq_iff_eq volume hsc continuous_const).1 hae
    have : ‖s x0‖ₑ ^ 2 = 0 := congrFun heq x0
    rw [pow_eq_zero_iff two_ne_zero, enorm_eq_zero, hs] at this
    exact ha0 this
  have hμV : μ V ≠ 0 := hVo.measure_ne_zero μ ⟨y0, fun i => rfl⟩
  have hle : (∫⁻ x, ‖s x‖ₑ ^ 2) * μ V ≤ l2A F μ D := by
    rw [← lintegral_indicator_const hVo.measurableSet]
    unfold l2A
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ V
    · rw [Set.indicator_of_mem hy]
      exact le_of_eq (lintegral_congr fun x => by rw [hV y hy x])
    · rw [Set.indicator_of_notMem hy]; exact bot_le
  rw [h0] at hle
  exact mul_ne_zero hc hμV (le_antisymm hle bot_le)

end GlobalTheory.WeilL2Words
end
