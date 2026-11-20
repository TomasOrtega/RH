import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageLatticeStabilizerParamsOffSetStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageConjugateValuesHeckeOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalOperatorEigenvaluesDeterminedByParamsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageLevelSphericalOffSetStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageCuspFormMapEqZeroOfValueZeroStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.ValPart

/- English proof (translation)
Apply `PiTensorProduct.ext` to reduce the goal to its premises. Use extensionality with `v`. Simplify using the standard rewrite rules.
-/
theorem lift_compMultilinearMap {ι : Type*} [Fintype ι] {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module ℂ (Mi i)]
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (L : E →ₗ[ℂ] F) (T : MultilinearMap ℂ Mi E) :
    PiTensorProduct.lift (L.compMultilinearMap T) = L ∘ₗ PiTensorProduct.lift T := by
  apply PiTensorProduct.ext
  ext v
  simp

/- English proof (translation)
Introduce `hCRD D hMet hLev c hc j hj s hs u w B hw hB`. Take `⟨-, hsphc, hsplit, -, hunif⟩` from `GlobalTheory.T.thetaChainStage_level_spherical_off_set D c hc j hj s hs`. Take `⟨-, hopc, hconjH⟩` from `GlobalTheory.T.thetaChainStage_conjugate_values_hecke_operators hCRD D c hc j hj s hs`. Establish `hlat` using `(GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc j hj s hs).2`. Take `⟨-, -, -, -, hmul, -⟩` from `hLev c hc j hj s hs`.

Establish `hBV : GlobalTheory.LFun.IsParamFunV s.V c.S (fun g => conj (PiLocalization₂.val u w g)) B` using `(hlat _ B).1 hB`. Take `⟨a, ha⟩` from `GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params D s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S hsphc B`. Establish `heig : ∀ P d R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R → heckeLin s.V R (PiLocalization₂.val u w) = conj (a P d) • PiLocalization₂.val u w`. Introduce `P d R hR`. Establish `h1` using `ha _ hBV P d R ((hopc P d R).1 hR)`.

Rewrite `h1` using `[hconjH]`. Use function extensionality and compare the values at `g`. Establish `h2` using `congrArg (starRingEnd ℂ) (congrFun h1 g)`. Simplify `h2` using `[map_mul]`. Establish `hops` using `GlobalTheory.SphericalOps.spherical_ops s.V c.θ s.M (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S hunif hc.inf hmul hsplit`.

Establish `hw0 : w ≠ 0`. Introduce and unpack `rfl`. Conclude with `hw (by simp [PiLocalization₂.val])`. Use `⟨fun P d => conj (a P d), ?_⟩` and prove the remaining obligations. Establish `hT : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L)` using `(mem_multT c.θ s.M _ _ _).1 u.2`.

Rewrite using `[mem_partFull]`. Use `⟨hT, fun P d R hR v => ?_⟩` and prove the remaining obligations. Take `⟨hkeep, -, -⟩` from `hops.2.2 P d R hR`. Use `set T := PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) with hTdef`. Establish `hT' : heckeOn s.M R T - conj (a P d) • T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L)` using `Submodule.sub_mem _ (hkeep T hT) (Submodule.smul_mem _ _ hT)`.

Establish `hmem : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) ∈ s.CC c` using `by show _ ∈ MultT c.θ s.M _ _`. Rewrite using `[mem_multT, LinearEquiv.symm_apply_apply]`. Conclude with `hT'`. Set `x : s.CC c` to `⟨_, hmem⟩`. Establish `hlift : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) = heckeLin s.V R ∘ₗ (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) - conj (a P d) • (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))`.

Rewrite using `[map_sub, map_smul, heckeOn, postOn]`. Simplify using `only [LinearMap.coe_mk, AddHom.coe_mk]`. Rewrite using `[lift_compMultilinearMap, hTdef, LinearEquiv.apply_symm_apply]`. Establish `hx : PiLocalization₂.val x w = 0` using `by show PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) w = 0`. Rewrite using `[hlift]`.

Simplify using `only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]`. Rewrite using `[sub_eq_zero]`. Conclude with `heig P d R hR`. Establish `hx0` using `GlobalTheory.T.thetaChainStage_cuspFormMap_eq_zero_of_value_zero D hMet c hc j hj s hs x w hw0 hx`. Establish `h3 : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) = 0` using `congrArg Subtype.val hx0`.

Establish `h4 : heckeOn s.M R T - conj (a P d) • T = 0`. Establish `h` using `congrArg PiTensorProduct.lift.symm h3`. Rewrite `h` using `[LinearEquiv.symm_apply_apply, map_zero]`. Then use the resulting hypothesis. Establish `h5` using `congrArg (fun U : MMap s.M => U v) h4`. Simplify using `only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, MultilinearMap.zero_apply, sub_eq_zero] at h5`.

Simplify `h5` using `[heckeOn, postOn_apply]`.
-/
theorem valPart_mem : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → LevFacts D → ForStage D fun c _ s =>
    ∀ (u : s.CC c) w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B →
      ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
        PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
          partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e := by
  intro hCRD D hMet hLev c hc j hj s hs u w B hw hB
  obtain ⟨-, hsphc, hsplit, -, hunif⟩ := GlobalTheory.T.thetaChainStage_level_spherical_off_set D c hc j hj s hs
  obtain ⟨-, hopc, hconjH⟩ := GlobalTheory.T.thetaChainStage_conjugate_values_hecke_operators hCRD D c hc j hj s hs
  have hlat := (GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc j hj s hs).2
  obtain ⟨-, -, -, -, hmul, -⟩ := hLev c hc j hj s hs
  have hBV : GlobalTheory.LFun.IsParamFunV s.V c.S (fun g => conj (PiLocalization₂.val u w g)) B := (hlat _ B).1 hB
  obtain ⟨a, ha⟩ := GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params D s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S hsphc B
  have heig : ∀ P d R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R →
      heckeLin s.V R (PiLocalization₂.val u w) = conj (a P d) • PiLocalization₂.val u w := by
    intro P d R hR
    have h1 := ha _ hBV P d R ((hopc P d R).1 hR)
    rw [hconjH] at h1
    funext g
    have h2 := congrArg (starRingEnd ℂ) (congrFun h1 g)
    simpa [map_mul] using h2
  have hops := GlobalTheory.SphericalOps.spherical_ops s.V c.θ s.M (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S
    hunif hc.inf hmul hsplit
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (by simp [PiLocalization₂.val])
  refine ⟨fun P d => conj (a P d), ?_⟩
  have hT : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) :=
    (mem_multT c.θ s.M _ _ _).1 u.2
  rw [mem_partFull]
  refine ⟨hT, fun P d R hR v => ?_⟩
  obtain ⟨hkeep, -, -⟩ := hops.2.2 P d R hR
  set T := PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) with hTdef
  have hT' : heckeOn s.M R T - conj (a P d) • T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) :=
    Submodule.sub_mem _ (hkeep T hT) (Submodule.smul_mem _ _ hT)
  have hmem : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) ∈ s.CC c := by
    show _ ∈ MultT c.θ s.M _ _
    rw [mem_multT, LinearEquiv.symm_apply_apply]
    exact hT'
  let x : s.CC c := ⟨_, hmem⟩
  have hlift : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) =
      heckeLin s.V R ∘ₗ (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) - conj (a P d) • (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) := by
    rw [map_sub, map_smul, heckeOn, postOn]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [lift_compMultilinearMap, hTdef, LinearEquiv.apply_symm_apply]
  have hx : PiLocalization₂.val x w = 0 := by
    show PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) w = 0
    rw [hlift]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    rw [sub_eq_zero]
    exact heig P d R hR
  have hx0 := GlobalTheory.T.thetaChainStage_cuspFormMap_eq_zero_of_value_zero D hMet c hc j hj s hs x w hw0 hx
  have h3 : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) = 0 := congrArg Subtype.val hx0
  have h4 : heckeOn s.M R T - conj (a P d) • T = 0 := by
    have h := congrArg PiTensorProduct.lift.symm h3
    rwa [LinearEquiv.symm_apply_apply, map_zero] at h
  have h5 := congrArg (fun U : MMap s.M => U v) h4
  simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, MultilinearMap.zero_apply, sub_eq_zero] at h5
  simpa [heckeOn, postOn_apply] using h5

end GlobalTheory.ChainOnto.ValPart

end
