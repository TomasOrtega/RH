import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableOfRapidDecay

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm.HaarSplit

variable (F : Type) [Field F] [NumberField F] (κ : Type)

def splitE : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃+ (κ → AdeleRing (𝓞 F) F) where
  toFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  invFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  left_inv p := Prod.ext (funext fun i => RingEquiv.apply_symm_apply _ _) (funext fun i => rfl)
  right_inv x := funext fun i => Prod.ext (RingEquiv.symm_apply_apply _ _) rfl
  map_add' p q := funext fun i => Prod.ext (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i) (q.1 i)) rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem splitE_apply (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    splitE F κ p = fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) := rfl

/- English proof (translation)
Rewrite using `[show ⇑(splitE F κ) = fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) => fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) from rfl]`. Conclude with `continuous_pi fun i => ((GlobalTheory.Core.Rk.RapidInt.continuous_ofMixed F).comp ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)`.
-/
theorem continuous_splitE : Continuous (splitE F κ) := by
  rw [show ⇑(splitE F κ) = fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
    fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) from rfl]
  exact continuous_pi fun i => ((GlobalTheory.Core.Rk.RapidInt.continuous_ofMixed F).comp
    ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

/- English proof (translation)
Rewrite using `[show ⇑(splitE F κ).symm = fun x : κ → AdeleRing (𝓞 F) F => ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2) : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) from rfl]`. Conclude with `(continuous_pi fun i => (GlobalTheory.Core.Rk.RapidInt.continuous_toMixed F).comp (continuous_fst.comp (continuous_apply i))).prodMk (continuous_pi fun i => continuous_snd.comp (continuous_apply i))`.
-/
theorem continuous_splitE_symm : Continuous (splitE F κ).symm := by
  rw [show ⇑(splitE F κ).symm = fun x : κ → AdeleRing (𝓞 F) F =>
    ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2) :
      (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) from rfl]
  exact (continuous_pi fun i => (GlobalTheory.Core.Rk.RapidInt.continuous_toMixed F).comp
    (continuous_fst.comp (continuous_apply i))).prodMk (continuous_pi fun i => continuous_snd.comp (continuous_apply i))

/- English proof (translation)
Simplify using `only [GlobalTheory.WeilM.pureA, splitE_apply, RingEquiv.apply_symm_apply]`.
-/
theorem pureA_splitE (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    GlobalTheory.WeilM.pureA F f g (splitE F κ p) = f p.1 * g p.2 := by
  simp only [GlobalTheory.WeilM.pureA, splitE_apply, RingEquiv.apply_symm_apply]

/- English proof (translation)
Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f, g, hg, rfl⟩` from `hx`. Simplify using `only [pureA_splitE]`. Conclude with `(f.continuous.comp continuous_fst).mul (hg.1.continuous.comp continuous_snd)`.

Consider the case `zero => exact continuous_const`. Consider the case `add x x' _ _ hx hx' => exact hx.add hx'`. Consider the case `smul a x _ hx => exact hx.const_smul a`.
-/
theorem continuous_comp_splitE [Fintype κ] (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    Continuous fun p => Φ (splitE F κ p) := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    simp only [pureA_splitE]
    exact (f.continuous.comp continuous_fst).mul (hg.1.continuous.comp continuous_snd)
  | zero => exact continuous_const
  | add x x' _ _ hx hx' => exact hx.add hx'
  | smul a x _ hx => exact hx.const_smul a

/- English proof (translation)
The claim follows from `funext fun i => Prod.ext (add_zero _).symm rfl`.
-/
theorem splitE_add_finE (z : κ → mixedEmbedding.mixedSpace F) (y u : κ → FiniteAdeleRing (𝓞 F) F) :
    splitE F κ (z, y + u) = splitE F κ (z, y) + GlobalTheory.WeilAdm.finE F u :=
  funext fun i => Prod.ext (add_zero _).symm rfl

/- English proof (translation)
Use `haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd`. Conclude with `Measure.pi.isAddHaarMeasure _`.
-/
theorem volume_isAddHaar [Fintype κ] : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := by
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  exact Measure.pi.isAddHaarMeasure _

end GlobalTheory.WeilAdm.HaarSplit

namespace GlobalTheory.WeilAdm.HaarSplit

open GlobalTheory.WeilAdm.HaarSplit

/- English proof (translation)
Introduce `F _ _ κ _ g hg U hU`. Use `haveI := volume_isAddHaar F κ`. Use `haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance`. Use `haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F`. Use `haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F`.

Use `haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F`. Use `letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _`. Use `haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩`. Use `letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _`. Use `haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩`.

Use `haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable`. Use `set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν`. Use `haveI : SFinite ν := inferInstance`. Use `haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd`. Use `haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd`.

Use `haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance`. Use `haveI : ((volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure (volume : Measure (κ → mixedEmbedding.mixedSpace F)) ν`. Establish `hμH : Measure.IsAddHaarMeasure ((volume.prod ν).map (splitE F κ))` using `(splitE F κ).isAddHaarMeasure_map _ (continuous_splitE F κ) (continuous_splitE_symm F κ)`. Set `em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AdeleRing (𝓞 F) F)` to `(Homeomorph.mk (splitE F κ).toEquiv (continuous_splitE F κ) (continuous_splitE_symm F κ)).toMeasurableEquiv`. Establish `hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞, ∫⁻ x, h x ∂((volume.prod ν).map (splitE F κ)) = ∫⁻ p, h (splitE F κ p) ∂(volume.prod ν)` using `fun h => lintegral_map_equiv h em`.

Establish `hgc : Continuous g` using `hg.1.continuous`. Establish `hC : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≠ ⊤`. Establish `h1 : ∫⁻ y, ‖g y * g y‖ₑ ∂ν < ⊤` using `((hgc.mul hgc).integrable_of_hasCompactSupport (hg.2.mul_left (f := g))).2`. Use `ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h1)` and prove the remaining obligations. Rewrite using `[enorm_mul, sq]`.

Take `⟨K, hKc, hK0⟩` from `exists_compact_mem_nhds (0 : κ → FiniteAdeleRing (𝓞 F) F)`. Use `set S : Set (κ → FiniteAdeleRing (𝓞 F) F) := (U : Set _) ∩ K with hS`. Establish `hSm : MeasurableSet S` using `hU.measurableSet.inter hKc.isClosed.measurableSet`. Establish `hc0 : ν S ≠ 0`. Use `ne_of_gt (lt_of_lt_of_le ?_ (measure_mono (Set.inter_subset_inter_right _ interior_subset)))` and prove the remaining obligations.

Conclude with `(hU.inter isOpen_interior).measure_pos ν ⟨0, U.zero_mem, mem_interior_iff_mem_nhds.2 hK0⟩`. Establish `hcT : ν S ≠ ⊤` using `ne_top_of_le_ne_top hKc.measure_lt_top.ne (measure_mono Set.inter_subset_right)`. Use `⟨(volume.prod ν).map (splitE F κ), hμH, ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν, ν S, hC, hc0, hcT, ?_, ?_⟩` and prove the remaining obligations. Introduce `f`. Rewrite using `[hint]`.

Establish `e1 : ∀ p, ‖GlobalTheory.WeilM.pureA F f g (splitE F κ p)‖ₑ ^ 2 = ‖f p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2`. Introduce `p`. Rewrite using `[pureA_splitE, enorm_mul, mul_pow]`. Repeatedly rewrite using `[e1]`. Rewrite using `[lintegral_prod_mul (f.continuous.measurable.enorm.pow_const 2).aemeasurable (hgc.measurable.enorm.pow_const 2).aemeasurable, mul_comm]`.

Introduce `Φ hΦ hinv y`. Rewrite using `[hint]`. Establish `hHm : Measurable fun p => ‖Φ (splitE F κ p)‖ₑ ^ 2` using `(continuous_comp_splitE F κ Φ hΦ).measurable.enorm.pow_const 2`. Rewrite using `[lintegral_prod _ hHm.aemeasurable, ← lintegral_const_mul' _ _ hcT]`. Use `lintegral_mono fun z => ?_` and prove the remaining obligations.

Use `set T : Set (κ → FiniteAdeleRing (𝓞 F) F) := (fun y' => y' + -y) ⁻¹' S with hT`. Establish `hTm : MeasurableSet T` using `hSm.preimage (continuous_add_right (-y)).measurable`. Establish `hνT : ν T = ν S` using `measure_preimage_add_right ν (-y) S`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_indicator_const hTm, hνT, mul_comm]`.

Use `_ ≤ ∫⁻ y', ‖Φ (splitE F κ (z, y'))‖ₑ ^ 2 ∂ν := by`. Use `lintegral_mono fun y' => (Set.indicator_le (g := fun y' => ‖Φ (splitE F κ (z, y'))‖ₑ ^ 2) (fun a ha => le_of_eq ?_)) y'` and prove the remaining obligations. Establish `hu : a + -y ∈ U` using `ha.1`. Establish `ha' : a = y + (a + -y)` using `by abel`. Use `show ‖Φ (splitE F κ (z, y))‖ₑ ^ 2 = ‖Φ (splitE F κ (z, a))‖ₑ ^ 2`.

Rewrite using `[ha', splitE_add_finE, hinv _ _ hu]`.
-/
theorem haar_pure_slice_bounds : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) → ∀ U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
      ∃ μ : @Measure (κ → AdeleRing (𝓞 F) F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
        ∃ C c : ℝ≥0∞, C ≠ ⊤ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
          (∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∫⁻ x, ‖GlobalTheory.WeilM.pureA F f g x‖ₑ ^ 2 ∂μ ≤ C * ∫⁻ z, ‖f z‖ₑ ^ 2) ∧
          ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) →
            ∀ y, c * ∫⁻ z, ‖GlobalTheory.WeilAdm.slice F Φ y z‖ₑ ^ 2 ≤ ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ g hg U hU
  haveI := volume_isAddHaar F κ
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : SFinite ν := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : ((volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (κ → mixedEmbedding.mixedSpace F)) ν
  have hμH : Measure.IsAddHaarMeasure ((volume.prod ν).map (splitE F κ)) :=
    (splitE F κ).isAddHaarMeasure_map _ (continuous_splitE F κ) (continuous_splitE_symm F κ)
  let em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
    (Homeomorph.mk (splitE F κ).toEquiv (continuous_splitE F κ) (continuous_splitE_symm F κ)).toMeasurableEquiv
  have hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞,
      ∫⁻ x, h x ∂((volume.prod ν).map (splitE F κ)) = ∫⁻ p, h (splitE F κ p) ∂(volume.prod ν) :=
    fun h => lintegral_map_equiv h em

  have hgc : Continuous g := hg.1.continuous
  have hC : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
    have h1 : ∫⁻ y, ‖g y * g y‖ₑ ∂ν < ⊤ :=
      ((hgc.mul hgc).integrable_of_hasCompactSupport (hg.2.mul_left (f := g))).2
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h1)
    rw [enorm_mul, sq]

  obtain ⟨K, hKc, hK0⟩ := exists_compact_mem_nhds (0 : κ → FiniteAdeleRing (𝓞 F) F)
  set S : Set (κ → FiniteAdeleRing (𝓞 F) F) := (U : Set _) ∩ K with hS
  have hSm : MeasurableSet S := hU.measurableSet.inter hKc.isClosed.measurableSet
  have hc0 : ν S ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono (Set.inter_subset_inter_right _ interior_subset)))
    exact (hU.inter isOpen_interior).measure_pos ν ⟨0, U.zero_mem, mem_interior_iff_mem_nhds.2 hK0⟩
  have hcT : ν S ≠ ⊤ := ne_top_of_le_ne_top hKc.measure_lt_top.ne (measure_mono Set.inter_subset_right)
  refine ⟨(volume.prod ν).map (splitE F κ), hμH, ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν, ν S, hC, hc0, hcT, ?_, ?_⟩
  · intro f
    rw [hint]
    have e1 : ∀ p, ‖GlobalTheory.WeilM.pureA F f g (splitE F κ p)‖ₑ ^ 2 = ‖f p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2 := by
      intro p
      rw [pureA_splitE, enorm_mul, mul_pow]
    simp_rw [e1]
    rw [lintegral_prod_mul (f.continuous.measurable.enorm.pow_const 2).aemeasurable
      (hgc.measurable.enorm.pow_const 2).aemeasurable, mul_comm]
  · intro Φ hΦ hinv y
    rw [hint]
    have hHm : Measurable fun p => ‖Φ (splitE F κ p)‖ₑ ^ 2 :=
      (continuous_comp_splitE F κ Φ hΦ).measurable.enorm.pow_const 2
    rw [lintegral_prod _ hHm.aemeasurable, ← lintegral_const_mul' _ _ hcT]
    refine lintegral_mono fun z => ?_
    set T : Set (κ → FiniteAdeleRing (𝓞 F) F) := (fun y' => y' + -y) ⁻¹' S with hT
    have hTm : MeasurableSet T := hSm.preimage (continuous_add_right (-y)).measurable
    have hνT : ν T = ν S := measure_preimage_add_right ν (-y) S
    calc ν S * ‖GlobalTheory.WeilAdm.slice F Φ y z‖ₑ ^ 2
        = ∫⁻ y', T.indicator (fun _ => ‖GlobalTheory.WeilAdm.slice F Φ y z‖ₑ ^ 2) y' ∂ν := by
          rw [lintegral_indicator_const hTm, hνT, mul_comm]
      _ ≤ ∫⁻ y', ‖Φ (splitE F κ (z, y'))‖ₑ ^ 2 ∂ν := by
          refine lintegral_mono fun y' => (Set.indicator_le (g := fun y' => ‖Φ (splitE F κ (z, y'))‖ₑ ^ 2) (fun a ha => le_of_eq ?_)) y'
          have hu : a + -y ∈ U := ha.1
          have ha' : a = y + (a + -y) := by abel
          show ‖Φ (splitE F κ (z, y))‖ₑ ^ 2 = ‖Φ (splitE F κ (z, a))‖ₑ ^ 2
          rw [ha', splitE_add_finE, hinv _ _ hu]

end GlobalTheory.WeilAdm.HaarSplit
