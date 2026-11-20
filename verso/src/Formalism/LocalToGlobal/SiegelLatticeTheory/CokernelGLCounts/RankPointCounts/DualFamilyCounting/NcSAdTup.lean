import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSSplitSk
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousMeasureSplitting
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousHAIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.MemSpanRIffSplit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousCrdAllSymm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.IsCompactStabGLHat

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.AdTupPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures NumberField IsDedekindDomain MeasureTheory Topology
open Formalism.L2.SG.Pf.NcS.SplitSk
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

/- English proof (translation)
Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `hO : MassDataMassesW.KCptW.LatHatOpen` using `MassDataMassesW.KCptW.latHatOpen_of @MassDataMassesW.KCptW.stdHatOpen_holds`. Establish `hC : MassDataMassesW.KCptW.LatHatCompact` using `MassDataMassesW.KCptW.latHatCompact_of @MassDataMassesW.KCptW.stdHatCompact_holds`. Establish `hMo` using `hO (F := F) L hL.span_eq_top hL.fg`. Establish `hMc` using `hC (F := F) L hL.span_eq_top hL.fg`.

Establish `eK : (Kf σ J (L : Set (Fin n → E)) : Set (HA (Af F) σ J)) = incAf σ J ⁻¹' MassDataMassesW.KCptW.stabGLHat (F` using `F) (L : Set (Fin n → E)) := by`. Use extensionality with `g`. Conclude with `MassDataMassesW.KCptW.kf_iff σ J _ g`. Establish `hinc : Continuous (incAf σ J)` using `continuous_subtype_val`. Rewrite using `[eK]`.

Use `⟨?_, (MassDataMassesW.KCptW.isOpen_stabGLHat L hMc hMo).preimage hinc⟩` and prove the remaining obligations. Conclude with `(PI.AdicCompletionValuation.isClosed_HR (Af F) σ J).isClosedEmbedding_subtypeVal.isCompact_preimage (MassDataMassesW.KCptW.isCompact_stabGLHat L hL.span_eq_top hMc)`.
-/
theorem kf_compact_open (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    IsCompact (Kf σ J (L : Set (Fin n → E)) : Set (HA (Af F) σ J)) ∧
      IsOpen (Kf σ J (L : Set (Fin n → E)) : Set (HA (Af F) σ J)) := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hO : MassDataMassesW.KCptW.LatHatOpen :=
    MassDataMassesW.KCptW.latHatOpen_of @MassDataMassesW.KCptW.stdHatOpen_holds
  have hC : MassDataMassesW.KCptW.LatHatCompact :=
    MassDataMassesW.KCptW.latHatCompact_of @MassDataMassesW.KCptW.stdHatCompact_holds
  have hMo := hO (F := F) L hL.span_eq_top hL.fg
  have hMc := hC (F := F) L hL.span_eq_top hL.fg
  have eK : (Kf σ J (L : Set (Fin n → E)) : Set (HA (Af F) σ J)) =
      incAf σ J ⁻¹' MassDataMassesW.KCptW.stabGLHat (F := F) (L : Set (Fin n → E)) := by
    ext g
    exact MassDataMassesW.KCptW.kf_iff σ J _ g
  have hinc : Continuous (incAf σ J) := continuous_subtype_val
  rw [eK]
  refine ⟨?_, (MassDataMassesW.KCptW.isOpen_stabGLHat L hMc hMo).preimage hinc⟩
  exact (PI.AdicCompletionValuation.isClosed_HR (Af F) σ J).isClosedEmbedding_subtypeVal.isCompact_preimage
    (MassDataMassesW.KCptW.isCompact_stabGLHat L hL.span_eq_top hMc)

/- English proof (translation)
Establish `: T2Space (R ⊗[F] E)` using `PI.VolStabS.RestrProdG.t2_tensor_product R`. Establish `hmat : Continuous (fun g : HA R σ J => ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)))` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hact : Continuous (fun g : HA R σ J => g • ratTup (F` using `F) R X) := by`. Use `continuous_pi fun b => ?_` and prove the remaining obligations. Use `show Continuous (fun g : HA R σ J => ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).mulVec (ratTup (F := F) R X b))`.

Conclude with `hmat.matrix_mulVec continuous_const`. Conclude with `isClosed_eq hact continuous_const`.
-/
theorem isClosed_stabT (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [FiniteDimensional F E] {a : ℕ} (X : Fin a → Fin n → E) :
    IsClosed (stabT R σ J X : Set (HA R σ J)) := by
  have : T2Space (R ⊗[F] E) := PI.VolStabS.RestrProdG.t2_tensor_product R
  have hmat : Continuous (fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))) :=
    Units.continuous_val.comp continuous_subtype_val
  have hact : Continuous (fun g : HA R σ J => g • ratTup (F := F) R X) := by
    refine continuous_pi fun b => ?_
    show Continuous (fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).mulVec
        (ratTup (F := F) R X b))
    exact hmat.matrix_mulVec continuous_const
  exact isClosed_eq hact continuous_const

end Gen

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J hCM hJ`. Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `hmI : Measurable (haMap σ J (fstA F))` using `(PI.UnitaryGroupMassFormula.MeasWCore.continuous_haMap σ J (fstA F) (PI.UnitaryGroupMassFormula.MeasWCore.continuous_tensMap (AF F) (fstA F) PI.UnitaryGroupMassFormula.MeasWCore.continuous_fstA)).measurable`. Establish `hmF : Measurable (haMap σ J (sndA F))` using `(PI.UnitaryGroupMassFormula.MeasWCore.continuous_haMap σ J (sndA F) (PI.UnitaryGroupMassFormula.MeasWCore.continuous_tensMap (AF F) (sndA F) PI.UnitaryGroupMassFormula.MeasWCore.continuous_sndA)).measurable`. Establish `: SecondCountableTopology (HA (Ainf F) σ J)` using `PI.VolStabS.TopoAF.secondCountable_HA_of (Ainf F) σ J`.

Establish `: SecondCountableTopology (HA (Af F) σ J)` using `PI.VolStabS.TopoAF.secondCountable_HA_of (Af F) σ J`. Establish `: SigmaCompactSpace (HA (Ainf F) σ J)` using `sigmaCompactSpace_of_locallyCompact_secondCountable`. Establish `: SigmaCompactSpace (HA (Af F) σ J)` using `sigmaCompactSpace_of_locallyCompact_secondCountable`. Establish `hsub : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R] (r : ℕ) (P : Frame E n r) (μ : Measure (Hsub R σ J P)), μ.IsHaarMeasure → SFinite (amb μ)`. Introduce `R _ _ _ _ _ _ _ r P μ hμ`.

Establish `: SecondCountableTopology (HA R σ J)` using `PI.VolStabS.TopoAF.secondCountable_HA_of R σ J`. Establish `hcl : IsClosed (Hsub R σ J P : Set (HA R σ J))` using `isClosed_stabT σ J R (tupH P)`. Establish `: LocallyCompactSpace (Hsub R σ J P)` using `hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `: SecondCountableTopology (Hsub R σ J P)` using `Topology.IsEmbedding.subtypeVal.secondCountableTopology`. Establish `: SigmaCompactSpace (Hsub R σ J P)` using `sigmaCompactSpace_of_locallyCompact_secondCountable`.

Use `hμ` as an intermediate fact. Use `infer_instance`. Use `⟨hmI.prodMk hmF, fun g₁ g₂ => ⟨PI.UnitaryGroupMassFormula.MeasWCore.haPair σ J g₁ g₂, PI.UnitaryGroupMassFormula.MeasWCore.splitA_haPair σ J g₁ g₂⟩, ?_, ?_, ?_, fun g => (continuous_mul_left g).measurable, fun g => (continuous_mul_left g).measurable, fun μ hμ => by have := hμ; in …` and prove the remaining obligations. Introduce `a g X`. Prove the components needed by the constructor for the conclusion.

Use function extensionality and compare the values at `x i`. Express the relevant statement in the definitionally equal form `tensMap (E := E) (fstA F) (((HA.mat (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).mulVec (X x) i) = ((((HA.mat (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (tensMap (E := E) (fstA F))).mulVec (fun j => ten …`. Rewrite using `[RingHom.map_mulVec]`. Both sides reduce to the same expression. Use function extensionality and compare the values at `x i`.

Express the relevant statement in the definitionally equal form `tensMap (E := E) (sndA F) (((HA.mat (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).mulVec (X x) i) = ((((HA.mat (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (tensMap (E := E) (sndA F))).mulVec (fun j => ten …`. Rewrite using `[RingHom.map_mulVec]`. Both sides reduce to the same expression. Introduce `a X0`. Conclude with `⟨funext fun x => funext fun i => PI.VolStabS.RestrProdG.map_inclR (fstA F) (X0 x i),`.

Use function extensionality and compare the values at `fun x => funext fun i => PI.VolStabS.RestrProdG.map_inclR (sndA F) (X0 x i)⟩`. Introduce `a X Y h1 h2`. Use function extensionality and compare the values at `x i`. Establish `e : PI.UnitaryGroupMassFormula.MeasWCore.splT (X x i) = PI.UnitaryGroupMassFormula.MeasWCore.splT (Y x i)` using `Prod.ext (congrFun (congrFun h1 x) i) (congrFun (congrFun h2 x) i)`. Use `congrArg PI.UnitaryGroupMassFormula.MeasWCore.splInv e` as an intermediate fact.

Rewrite `this` using `[PI.UnitaryGroupMassFormula.MeasWCore.splInv_splT, PI.UnitaryGroupMassFormula.MeasWCore.splInv_splT]`. Then use the resulting hypothesis. Introduce and unpack `Λ ⟨L, hL, rfl⟩`. Conclude with `(kf_compact_open σ J L hL).2.measurableSet`. Introduce and unpack `Λ μf ⟨L, hL, rfl⟩ _ _ _ r P μ hμ`. Take `⟨hKc, hKo⟩` from `kf_compact_open σ J L hL`.

Establish `hcl : IsClosed (Hsub (Af F) σ J P : Set (HA (Af F) σ J))` using `isClosed_stabT σ J (Af F) (tupH P)`. Use `hμ` as an intermediate fact. Use `⟨hKo.preimage continuous_subtype_val |>.measure_pos μ ⟨1, (Kf σ J _).one_mem⟩, ?_⟩` and prove the remaining obligations. Conclude with `(hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hKc).measure_lt_top`.
-/
theorem admissible_tuple_holds : AdTup := by
  intro F E _ _ _ _ _ σ n J hCM hJ
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hmI : Measurable (haMap σ J (fstA F)) :=
    (PI.UnitaryGroupMassFormula.MeasWCore.continuous_haMap σ J (fstA F)
      (PI.UnitaryGroupMassFormula.MeasWCore.continuous_tensMap (AF F) (fstA F) PI.UnitaryGroupMassFormula.MeasWCore.continuous_fstA)).measurable
  have hmF : Measurable (haMap σ J (sndA F)) :=
    (PI.UnitaryGroupMassFormula.MeasWCore.continuous_haMap σ J (sndA F)
      (PI.UnitaryGroupMassFormula.MeasWCore.continuous_tensMap (AF F) (sndA F) PI.UnitaryGroupMassFormula.MeasWCore.continuous_sndA)).measurable
  have : SecondCountableTopology (HA (Ainf F) σ J) :=
    PI.VolStabS.TopoAF.secondCountable_HA_of (Ainf F) σ J
  have : SecondCountableTopology (HA (Af F) σ J) :=
    PI.VolStabS.TopoAF.secondCountable_HA_of (Af F) σ J
  have : SigmaCompactSpace (HA (Ainf F) σ J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SigmaCompactSpace (HA (Af F) σ J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hsub : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
      [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R] (r : ℕ) (P : Frame E n r)
      (μ : Measure (Hsub R σ J P)), μ.IsHaarMeasure → SFinite (amb μ) := by
    intro R _ _ _ _ _ _ _ r P μ hμ
    have : SecondCountableTopology (HA R σ J) := PI.VolStabS.TopoAF.secondCountable_HA_of R σ J
    have hcl : IsClosed (Hsub R σ J P : Set (HA R σ J)) := isClosed_stabT σ J R (tupH P)
    have : LocallyCompactSpace (Hsub R σ J P) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
    have : SecondCountableTopology (Hsub R σ J P) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
    have : SigmaCompactSpace (Hsub R σ J P) := sigmaCompactSpace_of_locallyCompact_secondCountable
    have := hμ
    infer_instance
  refine ⟨hmI.prodMk hmF, fun g₁ g₂ => ⟨PI.UnitaryGroupMassFormula.MeasWCore.haPair σ J g₁ g₂,
      PI.UnitaryGroupMassFormula.MeasWCore.splitA_haPair σ J g₁ g₂⟩, ?_, ?_, ?_, fun g => (continuous_mul_left g).measurable,
    fun g => (continuous_mul_left g).measurable, fun μ hμ => by have := hμ; infer_instance,
    fun μ hμ => by have := hμ; infer_instance, fun r P μ hμ => hsub (Ainf F) r P μ hμ,
    fun r P μ hμ => hsub (Af F) r P μ hμ, ?_, ?_⟩
  · intro a g X
    constructor
    · funext x i
      change tensMap (E := E) (fstA F)
          (((HA.mat (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).mulVec (X x) i) =
        ((((HA.mat (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map
          (tensMap (E := E) (fstA F))).mulVec (fun j => tensMap (E := E) (fstA F) (X x j))) i
      rw [RingHom.map_mulVec]
      rfl
    · funext x i
      change tensMap (E := E) (sndA F)
          (((HA.mat (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).mulVec (X x) i) =
        ((((HA.mat (AF F) σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map
          (tensMap (E := E) (sndA F))).mulVec (fun j => tensMap (E := E) (sndA F) (X x j))) i
      rw [RingHom.map_mulVec]
      rfl
  · intro a X0
    exact ⟨funext fun x => funext fun i => PI.VolStabS.RestrProdG.map_inclR (fstA F) (X0 x i),
      funext fun x => funext fun i => PI.VolStabS.RestrProdG.map_inclR (sndA F) (X0 x i)⟩
  · intro a X Y h1 h2
    funext x i
    have e : PI.UnitaryGroupMassFormula.MeasWCore.splT (X x i) = PI.UnitaryGroupMassFormula.MeasWCore.splT (Y x i) :=
      Prod.ext (congrFun (congrFun h1 x) i) (congrFun (congrFun h2 x) i)
    have := congrArg PI.UnitaryGroupMassFormula.MeasWCore.splInv e
    rwa [PI.UnitaryGroupMassFormula.MeasWCore.splInv_splT, PI.UnitaryGroupMassFormula.MeasWCore.splInv_splT] at this
  · rintro Λ ⟨L, hL, rfl⟩
    exact (kf_compact_open σ J L hL).2.measurableSet
  · rintro Λ μf ⟨L, hL, rfl⟩ _ _ _ r P μ hμ
    obtain ⟨hKc, hKo⟩ := kf_compact_open σ J L hL
    have hcl : IsClosed (Hsub (Af F) σ J P : Set (HA (Af F) σ J)) := isClosed_stabT σ J (Af F) (tupH P)
    have := hμ
    refine ⟨hKo.preimage continuous_subtype_val |>.measure_pos μ ⟨1, (Kf σ J _).one_mem⟩, ?_⟩
    exact (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hKc).measure_lt_top

end Formalism.L2.SG.Pf.NcS.AdTupPf
