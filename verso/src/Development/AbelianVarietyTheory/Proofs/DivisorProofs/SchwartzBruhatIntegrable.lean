import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergWordL2Bound

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.WeilM

open scoped Classical

/- English proof (translation)
Use `letI mA : MeasurableSpace (κ → AF F) := borel _`. Use `haveI : BorelSpace (κ → AF F) := ⟨rfl⟩`. Use `haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F`. Use `haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Use `haveI := GlobalTheory.WeilAdm.HaarSplit.volume_isAddHaar F κ`.

Use `haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance`. Use `haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F`. Use `haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F`. Use `haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F`. Use `letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _`.

Use `haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩`. Use `haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable`. Use `set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν`. Use `haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd`. Use `haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd`.

Use `haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance`. Use `haveI := Measure.prod.instIsAddHaarMeasure (volume : Measure (κ → mixedEmbedding.mixedSpace F)) ν`. Use `haveI hρ : Measure.IsAddHaarMeasure ((volume.prod ν).map (GlobalTheory.WeilAdm.HaarSplit.splitE F κ)) := (GlobalTheory.WeilAdm.HaarSplit.splitE F κ).isAddHaarMeasure_map _ (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE F κ) (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE_sym …`. Set `em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AF F)` to `(Homeomorph.mk (GlobalTheory.WeilAdm.HaarSplit.splitE F κ).toEquiv (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE F κ) (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE_symm F κ)).toMeasurableEquiv`. Establish `hgi : Integrable g ν` using `hg.1.continuous.integrable_of_hasCompactSupport hg.2`.

Establish `hρi : Integrable (pureA F f g) ((volume.prod ν).map (GlobalTheory.WeilAdm.HaarSplit.splitE F κ))`. Establish `e : ((volume.prod ν).map (GlobalTheory.WeilAdm.HaarSplit.splitE F κ)) = (volume.prod ν).map em` using `rfl`. Rewrite using `[e, integrable_map_equiv em]`. Establish `e2 : pureA F f g ∘ em = fun p => f p.1 * g p.2` using `funext fun p => GlobalTheory.WeilAdm.HaarSplit.pureA_splitE F κ f g p`. Rewrite using `[e2]`.

Conclude with `(f.integrable (μ := volume)).mul_prod hgi`. Rewrite using `[Measure.isAddLeftInvariant_eq_smul μ ((volume.prod ν).map (GlobalTheory.WeilAdm.HaarSplit.splitE F κ))]`. Conclude with `hρi.smul_measure ENNReal.coe_ne_top`.
-/
theorem integrable_pureA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (f : SInf F κ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    @Integrable _ _ _ _ (borel _) (pureA F f g) μ := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.WeilAdm.HaarSplit.volume_isAddHaar F κ
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI := Measure.prod.instIsAddHaarMeasure (volume : Measure (κ → mixedEmbedding.mixedSpace F)) ν
  haveI hρ : Measure.IsAddHaarMeasure ((volume.prod ν).map (GlobalTheory.WeilAdm.HaarSplit.splitE F κ)) :=
    (GlobalTheory.WeilAdm.HaarSplit.splitE F κ).isAddHaarMeasure_map _ (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE F κ)
      (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE_symm F κ)
  let em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AF F) :=
    (Homeomorph.mk (GlobalTheory.WeilAdm.HaarSplit.splitE F κ).toEquiv (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE F κ)
      (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE_symm F κ)).toMeasurableEquiv
  have hgi : Integrable g ν := hg.1.continuous.integrable_of_hasCompactSupport hg.2
  have hρi : Integrable (pureA F f g) ((volume.prod ν).map (GlobalTheory.WeilAdm.HaarSplit.splitE F κ)) := by
    have e : ((volume.prod ν).map (GlobalTheory.WeilAdm.HaarSplit.splitE F κ)) = (volume.prod ν).map em := rfl
    rw [e, integrable_map_equiv em]
    have e2 : pureA F f g ∘ em = fun p => f p.1 * g p.2 := funext fun p =>
      GlobalTheory.WeilAdm.HaarSplit.pureA_splitE F κ f g p
    rw [e2]
    exact (f.integrable (μ := volume)).mul_prod hgi
  rw [Measure.isAddLeftInvariant_eq_smul μ ((volume.prod ν).map (GlobalTheory.WeilAdm.HaarSplit.splitE F κ))]
  exact hρi.smul_measure ENNReal.coe_ne_top

/- English proof (translation)
Introduce `F _ _ κ _`. Use `letI : MeasurableSpace (κ → AF F) := borel _`. Introduce `μ hμ Φ hΦ`. Take `⟨n, g, f, hg, rfl⟩` from `GlobalTheory.ThetaSobolevBase.exists_sumPure hΦ`. Conclude with `integrable_finsetSum' _ fun i _ => integrable_pureA μ hμ (f i) (hg i)`.
-/
theorem schA_integrable : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AF F) := borel _
    ∀ μY : Measure (κ → AF F), μY.IsAddHaarMeasure → ∀ φ ∈ schA F κ, Integrable φ μY := by
  intro F _ _ κ _
  letI : MeasurableSpace (κ → AF F) := borel _
  intro μ hμ Φ hΦ
  obtain ⟨n, g, f, hg, rfl⟩ := GlobalTheory.ThetaSobolevBase.exists_sumPure hΦ
  exact integrable_finsetSum' _ fun i _ => integrable_pureA μ hμ (f i) (hg i)

end GlobalTheory.WeilM

end
