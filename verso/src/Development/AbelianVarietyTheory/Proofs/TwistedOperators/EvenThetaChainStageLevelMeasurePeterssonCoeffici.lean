import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PushforwardHaarRealPointsTimesLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactFiniteAdelicSubgroupIntegralOpen
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapRestrictIsHaarOfOpenProductCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceEquivariantRealPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto.MeasPet

variable {D : D7}

open GlobalTheory.ChainOnto.HaarInf in

/- English proof (translation)
Introduce `D c hc j hj s hs`. Use `haveI := hs.haar`. Use `set V := s.V`. Set `K : Subgroup (GA D V)` to `s.J`. Set `Lf : Subgroup (GfC V)` to `K.subgroupOf (GfC V)`.

Set `A : Subgroup (GA D V)` to `Lf.comap (GlobalTheory.AutMult.toFin V)`. Establish `hfinK : ∀ g ∈ A, (GlobalTheory.AutMult.toFin V g : GA D V) ∈ K` using `fun g hg => Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hg)`. Establish `hAset : (A : Set (GA D V)) = s.big`. Use extensionality with `g`. Use `⟨fun hg => ⟨GlobalTheory.AutMult.toInf V g, GlobalTheory.AutMult.toFin V g, hfinK g hg, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨b, κ, hκ, rfl⟩`. Use `Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 ?_)` and prove the remaining obligations. Establish `e : GlobalTheory.AutMult.toFin V (κ : GA D V) = ⟨κ, hs.fin hκ⟩` using `GlobalTheory.AutMult.toFin_coe (⟨κ, hs.fin hκ⟩ : GfC V)`. Rewrite using `[map_mul, GlobalTheory.AutMult.toFin_coe_inf, one_mul, e]`. Conclude with `hκ`.

Establish `hLf : IsOpen (Lf : Set (GfC V))`. Take `⟨U, hU, hUK⟩` from `hs.isOpen`. Use `Subgroup.isOpen_mono (H₁ := U.subgroupOf (GfC V)) (fun k hk => ?_) (hU.preimage continuous_subtype_val)` and prove the remaining obligations. Conclude with `Subgroup.mem_subgroupOf.2 (hUK _ (Subgroup.mem_subgroupOf.1 hk) k.2)`. Establish `hAopen : IsOpen (A : Set (GA D V))` using `hLf.preimage (GlobalTheory.AutMult.continuous_toFin V)`.

Establish `hAint : (A : Set (GA D V)) ⊆ intOff c s`. Introduce `g hg v _`. Rewrite using `[← GlobalTheory.AutMult.toInf_mul_toFin g, map_mul, proj_of_mem_ginfC, one_mul]`. Conclude with `hs.stab _ (hfinK g hg) v`. Set `I : Subgroup (GA D V)` to `{ carrier := intOff c s mul_mem' := fun {a b} ha hb v hv => by rw [map_mul]; exact mul_mem (ha v hv) (hb v hv) one_mem' := fun v _ => by rw [map_one]; exact one_mem _ inv_mem' := fun {a} ha v hv => by rw [map_inv]; exact inv_mem (ha v hv) }`.

Establish `hIopen : IsOpen (I : Set (GA D V))` using `Subgroup.isOpen_mono (H₁ := A) hAint hAopen`. Establish `hker : {g : GA D V | g ∈ A ∧ GlobalTheory.AutMult.toInf V g = 1} = (K : Set (GA D V))`. Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, toInf_eq_one_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hgA, hgf⟩`. Use `hfinK g hgA` as an intermediate fact. Rewrite `this` using `[show (GlobalTheory.AutMult.toFin V g : GA D V) = g from congrArg Subtype.val (GlobalTheory.AutMult.toFin_coe (⟨g, hgf⟩ : GfC V))]`. Then use the resulting hypothesis. Introduce `hg`. Use `⟨?_, hs.fin hg⟩` and prove the remaining obligations.

Use `Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 ?_)` and prove the remaining obligations. Rewrite using `[show (GlobalTheory.AutMult.toFin V g : GA D V) = g from congrArg Subtype.val (GlobalTheory.AutMult.toFin_coe (⟨g, hs.fin hg⟩ : GfC V))]`. Conclude with `hg`. Establish `hKc : IsCompact (K : Set (GA D V))` using `GlobalTheory.ChainOnto.isCompact_of_integral_open D V s.Λ hs.selfDual K hs.fin hs.stab hs.isOpen`. Establish `hpi : ∀ b : GinfC V, GlobalTheory.AutMult.toInf V ((GinfC V).subtype b) = b` using `fun b => GlobalTheory.AutMult.toInf_coe b`.

Establish `hiA : ∀ b : GinfC V, (GinfC V).subtype b ∈ A` using `fun b => by`. Rewrite using `[← SetLike.mem_coe, hAset]`. Conclude with `⟨b, 1, one_mem _, by simp⟩`. Establish `hHaar : (Measure.map (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V)))).IsHaarMeasure` using `GlobalTheory.ChainOnto.map_restrict_isHaar (GA D V) (GinfC V) s.ν A (GinfC V).subtype (GlobalTheory.AutMult.toInf V) hAopen continuous_subtype_val (GlobalTheory.AutMult.continuous_toInf V) hpi hiA (hker ▸ hKc)`. Use `⟨⟨hIopen.measurableSet, hAset ▸ hAopen.measurableSet, hAset ▸ hAint, _, hHaar, fun f F hf hF => ?_⟩, ?_⟩` and prove the remaining obligations.

Establish `hmeas : AEMeasurable (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V)))` using `(GlobalTheory.AutMult.continuous_toInf V).measurable.aemeasurable`. Establish `hFA : ∀ g ∈ (A : Set (GA D V)), F g = f (GlobalTheory.AutMult.toInf V g)` using `fun g hg => by conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]`. Conclude with `hF _ _ (hfinK g hg)`. Establish `hint : IntegrableOn (fun g => f (GlobalTheory.AutMult.toInf V g)) (A : Set (GA D V)) s.ν` using `(integrable_map_measure hf.aestronglyMeasurable hmeas).1 hf`. Rewrite using `[← hAset]`.

Use `⟨hint.congr_fun (fun g hg => (hFA g hg).symm) hAopen.measurableSet, ?_⟩` and prove the remaining obligations. Rewrite using `[setIntegral_congr_fun hAopen.measurableSet hFA, integral_map hmeas hf.aestronglyMeasurable]`. Introduce `ipD ip hM u v b κ hκ`. Establish `hmem` using `(mem_multT c.θ s.M (s.J : Set (GA D V)) 1 (u : SmT s.M →ₗ[ℂ] (GA D V → ℂ))).1 u.2`. Establish `hmap` using `(GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem`.

Take `⟨w, hw, hU⟩` from `GlobalTheory.ChainOnto.mult_equiv_real D c.θ s.V s.par s.M (s.J : Set (GA D V)) 1 hc.inf v b`. Establish `hUw` using `hU _ hmem`. Establish `ev : ∀ x : s.M.Vec, PiLocalization₂.val u (PiTensorProduct.tprod ℂ x) = PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D V → ℂ)) x`. Introduce `x`. Simplify using `[PiLocalization₂.val, PiTensorProduct.lift_symm]`.

Establish `key : rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = PiLocalization₂.val u (PiTensorProduct.tprod ℂ w)`. Use function extensionality and compare the values at `g`. Rewrite using `[ev, ev, hUw]`. Simplify using `only [rTr]`. Rewrite using `[← mul_assoc]`.

Simplify using `using hmap.lev v κ hκ (g * (b : GA D s.V))`. Establish `hsch : s.pet (PiLocalization₂.val u (PiTensorProduct.tprod ℂ w)) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = ip u u * ipD (PiTensorProduct.tprod ℂ w) (PiTensorProduct.tprod ℂ v)` using `hM.schur u u _ _`. Rewrite using `[key, hsch, hM.pure w v]`. Simplify using `only [hw]`.
-/
theorem meas_petco : ∀ D : D7, ForStage D fun c _ s => (MeasurableSet (intOff c s) ∧ MeasurableSet s.big ∧ s.big ⊆ intOff c s ∧ ∃ mR : Measure (GinfC s.V), mR.IsHaarMeasure ∧ ∀ (f : GinfC s.V → ℂ) (F : GA D s.V → ℂ), Integrable f mR → (∀ (b : GinfC s.V), ∀ κ ∈ s.J, F ((b : GA D s.V) * κ) = f b) → IntegrableOn F s.big s.ν ∧ ∫ g in s.big, F g ∂s.ν = ∫ b, f b ∂mR) ∧ ∀ ipD ip, IsMet c s ipD ip → ∀ (u : s.CC c) (v : s.M.Vec) (b : GinfC s.V), ∀ κ ∈ s.J, s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = ip u u * ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  intro D c hc j hj s hs
  haveI := hs.haar
  set V := s.V
  let K : Subgroup (GA D V) := s.J
  let Lf : Subgroup (GfC V) := K.subgroupOf (GfC V)
  let A : Subgroup (GA D V) := Lf.comap (GlobalTheory.AutMult.toFin V)
  have hfinK : ∀ g ∈ A, (GlobalTheory.AutMult.toFin V g : GA D V) ∈ K := fun g hg => Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hg)
  have hAset : (A : Set (GA D V)) = s.big := by
    ext g
    refine ⟨fun hg => ⟨GlobalTheory.AutMult.toInf V g, GlobalTheory.AutMult.toFin V g, hfinK g hg, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩, ?_⟩
    rintro ⟨b, κ, hκ, rfl⟩
    refine Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 ?_)
    have e : GlobalTheory.AutMult.toFin V (κ : GA D V) = ⟨κ, hs.fin hκ⟩ := GlobalTheory.AutMult.toFin_coe (⟨κ, hs.fin hκ⟩ : GfC V)
    rw [map_mul, GlobalTheory.AutMult.toFin_coe_inf, one_mul, e]
    exact hκ
  have hLf : IsOpen (Lf : Set (GfC V)) := by
    obtain ⟨U, hU, hUK⟩ := hs.isOpen
    refine Subgroup.isOpen_mono (H₁ := U.subgroupOf (GfC V)) (fun k hk => ?_) (hU.preimage continuous_subtype_val)
    exact Subgroup.mem_subgroupOf.2 (hUK _ (Subgroup.mem_subgroupOf.1 hk) k.2)
  have hAopen : IsOpen (A : Set (GA D V)) := hLf.preimage (GlobalTheory.AutMult.continuous_toFin V)
  have hAint : (A : Set (GA D V)) ⊆ intOff c s := by
    intro g hg v _
    rw [← GlobalTheory.AutMult.toInf_mul_toFin g, map_mul, proj_of_mem_ginfC, one_mul]
    exact hs.stab _ (hfinK g hg) v
  let I : Subgroup (GA D V) :=
    { carrier := intOff c s
      mul_mem' := fun {a b} ha hb v hv => by rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)
      one_mem' := fun v _ => by rw [map_one]; exact one_mem _
      inv_mem' := fun {a} ha v hv => by rw [map_inv]; exact inv_mem (ha v hv) }
  have hIopen : IsOpen (I : Set (GA D V)) := Subgroup.isOpen_mono (H₁ := A) hAint hAopen
  have hker : {g : GA D V | g ∈ A ∧ GlobalTheory.AutMult.toInf V g = 1} = (K : Set (GA D V)) := by
    ext g
    simp only [Set.mem_setOf_eq, toInf_eq_one_iff]
    constructor
    · rintro ⟨hgA, hgf⟩
      have := hfinK g hgA
      rwa [show (GlobalTheory.AutMult.toFin V g : GA D V) = g from congrArg Subtype.val (GlobalTheory.AutMult.toFin_coe (⟨g, hgf⟩ : GfC V))] at this
    · intro hg
      refine ⟨?_, hs.fin hg⟩
      refine Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 ?_)
      rw [show (GlobalTheory.AutMult.toFin V g : GA D V) = g from congrArg Subtype.val (GlobalTheory.AutMult.toFin_coe (⟨g, hs.fin hg⟩ : GfC V))]
      exact hg
  have hKc : IsCompact (K : Set (GA D V)) :=
    GlobalTheory.ChainOnto.isCompact_of_integral_open D V s.Λ hs.selfDual K hs.fin hs.stab hs.isOpen
  have hpi : ∀ b : GinfC V, GlobalTheory.AutMult.toInf V ((GinfC V).subtype b) = b := fun b => GlobalTheory.AutMult.toInf_coe b
  have hiA : ∀ b : GinfC V, (GinfC V).subtype b ∈ A := fun b => by
    rw [← SetLike.mem_coe, hAset]
    exact ⟨b, 1, one_mem _, by simp⟩
  have hHaar : (Measure.map (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V)))).IsHaarMeasure :=
    GlobalTheory.ChainOnto.map_restrict_isHaar (GA D V) (GinfC V) s.ν A (GinfC V).subtype (GlobalTheory.AutMult.toInf V) hAopen
      continuous_subtype_val (GlobalTheory.AutMult.continuous_toInf V) hpi hiA (hker ▸ hKc)
  refine ⟨⟨hIopen.measurableSet, hAset ▸ hAopen.measurableSet, hAset ▸ hAint, _, hHaar, fun f F hf hF => ?_⟩, ?_⟩
  · have hmeas : AEMeasurable (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V))) :=
      (GlobalTheory.AutMult.continuous_toInf V).measurable.aemeasurable
    have hFA : ∀ g ∈ (A : Set (GA D V)), F g = f (GlobalTheory.AutMult.toInf V g) := fun g hg => by
      conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
      exact hF _ _ (hfinK g hg)
    have hint : IntegrableOn (fun g => f (GlobalTheory.AutMult.toInf V g)) (A : Set (GA D V)) s.ν :=
      (integrable_map_measure hf.aestronglyMeasurable hmeas).1 hf
    rw [← hAset]
    refine ⟨hint.congr_fun (fun g hg => (hFA g hg).symm) hAopen.measurableSet, ?_⟩
    rw [setIntegral_congr_fun hAopen.measurableSet hFA, integral_map hmeas hf.aestronglyMeasurable]
  · intro ipD ip hM u v b κ hκ
    have hmem := (mem_multT c.θ s.M (s.J : Set (GA D V)) 1 (u : SmT s.M →ₗ[ℂ] (GA D V → ℂ))).1 u.2
    have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
    obtain ⟨w, hw, hU⟩ := GlobalTheory.ChainOnto.mult_equiv_real D c.θ s.V s.par s.M (s.J : Set (GA D V)) 1 hc.inf v b
    have hUw := hU _ hmem
    have ev : ∀ x : s.M.Vec, PiLocalization₂.val u (PiTensorProduct.tprod ℂ x) =
        PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D V → ℂ)) x := by
      intro x; simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
    have key : rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) =
        PiLocalization₂.val u (PiTensorProduct.tprod ℂ w) := by
      funext g
      rw [ev, ev, hUw]
      simp only [rTr]
      rw [← mul_assoc]
      simpa using hmap.lev v κ hκ (g * (b : GA D s.V))
    have hsch : s.pet (PiLocalization₂.val u (PiTensorProduct.tprod ℂ w)) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) =
        ip u u * ipD (PiTensorProduct.tprod ℂ w) (PiTensorProduct.tprod ℂ v) := hM.schur u u _ _
    rw [key, hsch, hM.pure w v]
    simp only [hw]

end GlobalTheory.EvenOnto.MeasPet
