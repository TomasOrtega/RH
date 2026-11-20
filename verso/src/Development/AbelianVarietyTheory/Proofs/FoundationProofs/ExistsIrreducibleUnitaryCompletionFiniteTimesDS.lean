import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqBotOrEqOfStarProjectionEqSmul
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AutMult

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨v, hv⟩ -`. Establish `hmap : (Subtype.val '' (Submodule.span ℂ s : Set U) : Set K) = Submodule.span ℂ (Subtype.val '' s)`. Conclude with `congrArg (fun p : Submodule ℂ K => (p : Set K)) (Submodule.map_span U.subtype s)`. Establish `h2 : v ∈ closure (Subtype.val '' (Submodule.span ℂ s : Set U))`.

Rewrite using `[hmap, ← Submodule.topologicalClosure_coe]`. Conclude with `h hv`. Rewrite using `[← SetLike.mem_coe, Submodule.topologicalClosure_coe, Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage]`. Conclude with `h2`.
-/
theorem topologicalClosure_span_eq_top_of_le {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : Submodule ℂ K) (s : Set U)
    (h : U ≤ (Submodule.span ℂ (Subtype.val '' s)).topologicalClosure) :
    (Submodule.span ℂ s).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨v, hv⟩ -
  have hmap : (Subtype.val '' (Submodule.span ℂ s : Set U) : Set K) = Submodule.span ℂ (Subtype.val '' s) := by
    exact congrArg (fun p : Submodule ℂ K => (p : Set K)) (Submodule.map_span U.subtype s)
  have h2 : v ∈ closure (Subtype.val '' (Submodule.span ℂ s : Set U)) := by
    rw [hmap, ← Submodule.topologicalClosure_coe]
    exact h hv
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage]
  exact h2

/- English proof (translation)
Introduce `D V S M μ _ _ W _ _ σ hirr hadm hm`. Establish `hne : homFinDS σ M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ≠ ⊥` using `fun h => hm (by rw [mCuspDS, h]; simp)`. Take `⟨T, hT, hT0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Establish `hinj : Function.Injective T` using `injective_of_mem_homInto hirr hT hT0`. Establish `hTt : T ∈ homFinDS σ M (RG V μ) ⊤` using `homTensorPi_mono le_top hT`.

Take `⟨U, hUdef⟩ : ∃ U : Submodule ℂ (DividedPowerChartLift V μ), (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure = U` from `⟨_, rfl⟩`. Establish `hcopy : IsCopyFinDS σ M (RG V μ) U` using `⟨T, hTt, hinj, hUdef⟩`. Establish `hU` using `TrCopy.isIrredSubrep_of_isCopyFinDS D V S M W σ hirr hadm (DividedPowerChartLift V μ) (RG V μ) (isUnitaryRep_RG V μ) U hcopy`. Use `⟨U, inferInstance, inferInstance, hU.1.rep, isIrrUnitary_rep (isUnitaryRep_RG V μ) hU, ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ w y, T w y ∈ U` using `fun w y => hUdef ▸ Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, y, rfl⟩)`.

Set `T' : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H U` to `{ toFun := fun w => (T w).codRestrict U (hmem w) map_add' := fun a b => by ext y; simp map_smul' := fun c a => by ext y; simp }`. Establish `hT'v : ∀ w y, (T' w y : DividedPowerChartLift V μ) = T w y` using `fun _ _ => rfl`. Establish `hTm` using `mem_homTensorPi.1 hTt`. Use `⟨T', mem_homTensorPi.2 ⟨fun _ _ => trivial, fun g w y => Subtype.ext ?_, fun i g w y => Subtype.ext ?_⟩, fun a b h => hinj (ContinuousMultilinearMap.ext fun y => congrArg Subtype.val (DFunLike.congr_fun h y)), ?_⟩` and prove the remaining obligations. Conclude with `hTm.2.1 g w y`.

Conclude with `hTm.2.2 i g w y`. Establish `himg : Subtype.val '' {v : U | ∃ w y, v = T' w y} = {v | ∃ w y, v = T w y}`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨w, y, rfl⟩, rfl⟩`.

Conclude with `⟨w, y, rfl⟩`. Introduce and unpack `⟨w, y, rfl⟩`. Conclude with `⟨T' w y, ⟨w, y, rfl⟩, rfl⟩`. Conclude with `topologicalClosure_span_eq_top_of_le U _ (le_of_eq (by rw [himg]; exact hUdef.symm))`.
-/
theorem exists_isIrrUnitary_isCopyFinDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Type) [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → mCuspDS μ σ M ≠ 0 →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (π : GA D V →* (H →L[ℂ] H)),
      IsIrrUnitary π ∧ IsCopyFinDS σ M π ⊤ := by
  intro D V S M μ _ _ W _ _ σ hirr hadm hm
  classical
  have hne : homFinDS σ M (RG V μ) (GlobalTheory.Cusp.L2cusp V μ) ≠ ⊥ := fun h => hm (by rw [mCuspDS, h]; simp)
  obtain ⟨T, hT, hT0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hinj : Function.Injective T := injective_of_mem_homInto hirr hT hT0
  have hTt : T ∈ homFinDS σ M (RG V μ) ⊤ := homTensorPi_mono le_top hT
  obtain ⟨U, hUdef⟩ : ∃ U : Submodule ℂ (DividedPowerChartLift V μ), (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure = U :=
    ⟨_, rfl⟩
  have hcopy : IsCopyFinDS σ M (RG V μ) U := ⟨T, hTt, hinj, hUdef⟩
  have hU := TrCopy.isIrredSubrep_of_isCopyFinDS D V S M W σ hirr hadm (DividedPowerChartLift V μ) (RG V μ) (isUnitaryRep_RG V μ) U hcopy
  refine ⟨U, inferInstance, inferInstance, hU.1.rep, isIrrUnitary_rep (isUnitaryRep_RG V μ) hU, ?_⟩
  have hmem : ∀ w y, T w y ∈ U := fun w y =>
    hUdef ▸ Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, y, rfl⟩)
  let T' : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H U :=
    { toFun := fun w => (T w).codRestrict U (hmem w)
      map_add' := fun a b => by ext y; simp
      map_smul' := fun c a => by ext y; simp }
  have hT'v : ∀ w y, (T' w y : DividedPowerChartLift V μ) = T w y := fun _ _ => rfl
  have hTm := mem_homTensorPi.1 hTt
  refine ⟨T', mem_homTensorPi.2 ⟨fun _ _ => trivial, fun g w y => Subtype.ext ?_, fun i g w y => Subtype.ext ?_⟩,
    fun a b h => hinj (ContinuousMultilinearMap.ext fun y => congrArg Subtype.val (DFunLike.congr_fun h y)), ?_⟩
  · exact hTm.2.1 g w y
  · exact hTm.2.2 i g w y
  · have himg : Subtype.val '' {v : U | ∃ w y, v = T' w y} = {v | ∃ w y, v = T w y} := by
      ext x
      constructor
      · rintro ⟨_, ⟨w, y, rfl⟩, rfl⟩
        exact ⟨w, y, rfl⟩
      · rintro ⟨w, y, rfl⟩
        exact ⟨T' w y, ⟨w, y, rfl⟩, rfl⟩
    exact topologicalClosure_span_eq_top_of_le U _ (le_of_eq (by rw [himg]; exact hUdef.symm))

end GlobalTheory.AutMult
