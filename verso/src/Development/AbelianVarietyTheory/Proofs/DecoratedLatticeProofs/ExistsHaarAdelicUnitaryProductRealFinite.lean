import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdelicHaarProd

/- English proof (translation)
Introduce `D V μf hμf`. Take `⟨hLC, hSC, hT2, hB, hTG, -, -⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V`. Establish `hi` using `GlobalTheory.AdelicSplit.isClosed_GinfC' V`. Establish `hf` using `GlobalTheory.AdelicSplit.isClosed_GfC' V`. Use `haveI : LocallyCompactSpace (GinfC V) := hi.locallyCompactSpace`.

Use `haveI : LocallyCompactSpace (GfC V) := hf.locallyCompactSpace`. Set `e` to `GlobalTheory.AdelicSplit.splitEquiv V`. Set `μi : Measure (GinfC V)` to `Measure.haar`. Use `haveI : SFinite μf := inferInstance`. Use `⟨Measure.map e (μi.prod μf), μi, ContinuousMulEquiv.isHaarMeasure_map _ e, fun S E => ?_⟩` and prove the remaining obligations.

Establish `hset : {h : GA D V | ∃ a ∈ S, ∃ k ∈ E, h = (a : GA D V) * k} = e '' (S ×ˢ E)`. Use extensionality with `h`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, k, hk, rfl⟩`. Conclude with `⟨(a, k), ⟨ha, hk⟩, rfl⟩`.

Introduce and unpack `⟨p, ⟨ha, hk⟩, rfl⟩`. Conclude with `⟨p.1, ha, p.2, hk, rfl⟩`. Rewrite using `[hset]`. Rewrite using `[show (Measure.map e (μi.prod μf)) = Measure.map (e.toHomeomorph.toMeasurableEquiv) (μi.prod μf) from rfl]`. Rewrite using `[MeasurableEquiv.map_apply]`.

Rewrite using `[show (e.toHomeomorph.toMeasurableEquiv) ⁻¹' (e '' (S ×ˢ E)) = S ×ˢ E from e.toEquiv.preimage_image _]`. Conclude with `Measure.prod_prod S E`.
-/
theorem haar_prod : ∀ (D : D7) (V : HSp D) (μf : Measure (GfC V)), μf.IsHaarMeasure → ∃ (μR : Measure (GA D V)) (μi : Measure (GinfC V)), μR.IsHaarMeasure ∧ ∀ (S : Set (GinfC V)) (E : Set (GfC V)), μR {h | ∃ a ∈ S, ∃ k ∈ E, h = (a : GA D V) * k} = μi S * μf E := by
  intro D V μf hμf
  obtain ⟨hLC, hSC, hT2, hB, hTG, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hi := GlobalTheory.AdelicSplit.isClosed_GinfC' V
  have hf := GlobalTheory.AdelicSplit.isClosed_GfC' V
  haveI : LocallyCompactSpace (GinfC V) := hi.locallyCompactSpace
  haveI : LocallyCompactSpace (GfC V) := hf.locallyCompactSpace
  let e := GlobalTheory.AdelicSplit.splitEquiv V
  let μi : Measure (GinfC V) := Measure.haar
  haveI : SFinite μf := inferInstance
  refine ⟨Measure.map e (μi.prod μf), μi, ContinuousMulEquiv.isHaarMeasure_map _ e, fun S E => ?_⟩
  have hset : {h : GA D V | ∃ a ∈ S, ∃ k ∈ E, h = (a : GA D V) * k} = e '' (S ×ˢ E) := by
    ext h
    constructor
    · rintro ⟨a, ha, k, hk, rfl⟩
      exact ⟨(a, k), ⟨ha, hk⟩, rfl⟩
    · rintro ⟨p, ⟨ha, hk⟩, rfl⟩
      exact ⟨p.1, ha, p.2, hk, rfl⟩
  rw [hset]
  rw [show (Measure.map e (μi.prod μf)) = Measure.map (e.toHomeomorph.toMeasurableEquiv) (μi.prod μf) from rfl]
  rw [MeasurableEquiv.map_apply]
  rw [show (e.toHomeomorph.toMeasurableEquiv) ⁻¹' (e '' (S ×ˢ E)) = S ×ˢ E from e.toEquiv.preimage_image _]
  exact Measure.prod_prod S E

end GlobalTheory.AdelicHaarProd
