import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
open GlobalTheory.RegSS

open Formalism.UG NumberField Topology
open scoped TensorProduct

namespace GlobalTheory.RegSSLattice

open NumberField Topology in
open scoped TensorProduct in
/- English proof (translation)
Take `⟨U, hU, hUF⟩` from `_root_.GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F`. Establish `hsub : Filter.Tendsto (fun p : AdeleRing (𝓞 F) F × AdeleRing (𝓞 F) F => p.1 - p.2) (𝓝 (0, 0)) (𝓝 0)` using `(continuous_fst.sub continuous_snd).tendsto' _ _ (by simp)`. Establish `hpre : (fun p : AdeleRing (𝓞 F) F × AdeleRing (𝓞 F) F => p.1 - p.2) ⁻¹' U ∈ 𝓝 ((0 : AdeleRing (𝓞 F) F), (0 : AdeleRing (𝓞 F) F))` using `hsub hU`. Rewrite `hpre` using `[nhds_prod_eq]`. Take `⟨V, hV, W, hW, hVW⟩` from `Filter.mem_prod_iff.mp hpre`.

Establish `hVU : ∀ v ∈ V ∩ W, ∀ w ∈ V ∩ W, v - w ∈ U` using `fun v hv w hw => hVW (Set.mk_mem_prod hv.1 hw.2)`. Take `⟨t, -, ht⟩` from `hK.elim_nhds_subcover (fun k => {y | y - k ∈ V ∩ W}) fun k _ => (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using Filter.inter_mem hV hW)`. Use `(t.finite_toSet.biUnion (t := fun k => {c : F | algebraMap F (AdeleRing (𝓞 F) F) c - k ∈ V ∩ W}) fun k _ => ?_).subset fun c hc => ?_` and prove the remaining obligations. Use `Set.Subsingleton.finite fun c hc c' hc' => ?_` and prove the remaining obligations. Use `hUF (c - c') (by simpa [map_sub] using hVU _ hc _ hc')` as an intermediate fact.

Conclude with `sub_eq_zero.mp this`. Simplify using `using ht hc`.
-/
private lemma finite_setOf_algebraMap_mem_of_isCompact (F : Type) [Field F] [NumberField F]
    {K : Set (AdeleRing (𝓞 F) F)} (hK : IsCompact K) :
    {c : F | algebraMap F (AdeleRing (𝓞 F) F) c ∈ K}.Finite := by
  obtain ⟨U, hU, hUF⟩ := _root_.GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  have hsub : Filter.Tendsto (fun p : AdeleRing (𝓞 F) F × AdeleRing (𝓞 F) F => p.1 - p.2)
      (𝓝 (0, 0)) (𝓝 0) :=
    (continuous_fst.sub continuous_snd).tendsto' _ _ (by simp)
  have hpre : (fun p : AdeleRing (𝓞 F) F × AdeleRing (𝓞 F) F => p.1 - p.2) ⁻¹' U ∈
      𝓝 ((0 : AdeleRing (𝓞 F) F), (0 : AdeleRing (𝓞 F) F)) := hsub hU
  rw [nhds_prod_eq] at hpre
  obtain ⟨V, hV, W, hW, hVW⟩ := Filter.mem_prod_iff.mp hpre
  have hVU : ∀ v ∈ V ∩ W, ∀ w ∈ V ∩ W, v - w ∈ U := fun v hv w hw =>
    hVW (Set.mk_mem_prod hv.1 hw.2)
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun k => {y | y - k ∈ V ∩ W}) fun k _ =>
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      (by simpa using Filter.inter_mem hV hW)
  refine (t.finite_toSet.biUnion
    (t := fun k => {c : F | algebraMap F (AdeleRing (𝓞 F) F) c - k ∈ V ∩ W})
    fun k _ => ?_).subset fun c hc => ?_
  · refine Set.Subsingleton.finite fun c hc c' hc' => ?_
    have := hUF (c - c') (by simpa [map_sub] using hVU _ hc _ hc')
    exact sub_eq_zero.mp this
  · simpa using ht hc

open NumberField Topology in
open scoped TensorProduct in

/- English proof (translation)
Unfold `_root_.GlobalTheory.RegSS.TensorLattice`. Introduce `F B _ _ _ _ _`. Use `haveI := _root_.GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F`. Use `haveI := _root_.GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Use `haveI := _root_.GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`.

Take `⟨U, hU, hUF⟩` from `_root_.GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F`. Use `haveI : Nontrivial (AdeleRing (𝓞 F) F) := ⟨⟨0, 1, fun h01 => one_ne_zero (hUF 1 (by rw [map_one, ← h01]; exact mem_of_mem_nhds hU))⟩⟩`. Use `letI : Algebra (AdeleRing (𝓞 F) F) (B ⊗[F] AdeleRing (𝓞 F) F) := Algebra.TensorProduct.rightAlgebra`. Use `letI : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) := _root_.Formalism.BasicNotions.tensTopL (AdeleRing (𝓞 F) F)`. Use `haveI : IsModuleTopology (AdeleRing (𝓞 F) F) (B ⊗[F] AdeleRing (𝓞 F) F) := ⟨rfl⟩`.

Use `haveI : ContinuousAdd (B ⊗[F] AdeleRing (𝓞 F) F) := IsModuleTopology.toContinuousAdd (AdeleRing (𝓞 F) F) _`. Set `b` to `Module.finBasis F B`. Set `c : B ⊗[F] AdeleRing (𝓞 F) F ≃ₗ[AdeleRing (𝓞 F) F] AdeleRing (𝓞 F) F ⊗[F] B` to `{ TensorProduct.comm F B (AdeleRing (𝓞 F) F) with map_smul' := fun a t => by`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x y`. Express the relevant statement in the definitionally equal form `TensorProduct.comm F B _ (a • (x ⊗ₜ y)) = a • TensorProduct.comm F B _ (x ⊗ₜ y)`. Rewrite using `[Algebra.smul_def]`. Simplify using `[Algebra.TensorProduct.right_algebraMap_apply, TensorProduct.smul_tmul', mul_comm]`. Consider the case `add x y hx hy => simp_all [smul_add] }`.

Set `e` to `c.trans (Algebra.TensorProduct.basis (AdeleRing (𝓞 F) F) b).equivFun`. Use `haveI : Module.Finite (AdeleRing (𝓞 F) F) (B ⊗[F] AdeleRing (𝓞 F) F) := Module.Finite.of_basis ((Algebra.TensorProduct.basis (AdeleRing (𝓞 F) F) b).map c.symm)`. Set `h : B ⊗[F] AdeleRing (𝓞 F) F ≃L[AdeleRing (𝓞 F) F] (Fin (Module.finrank F B) → AdeleRing (𝓞 F) F)` to `{ e with continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }`. Establish `he : ∀ β : B, h (_root_.Formalism.UG.inclE (AdeleRing (𝓞 F) F) β) = fun i => algebraMap F (AdeleRing (𝓞 F) F) (b.equivFun β i)`. Introduce `β`.

Use extensionality with `i`. Use `show e (β ⊗ₜ 1) i = _`. Simplify using `[e, c, Algebra.TensorProduct.basis_repr_tmul]`. Use `⟨IsModuleTopology.isTopologicalRing (AdeleRing (𝓞 F) F) _, h.toHomeomorph.isClosedEmbedding.locallyCompactSpace, h.toHomeomorph.isEmbedding.t2Space, h.toHomeomorph.secondCountableTopology, _root_.Formalism.UG.P.inclE_injective F B (AdeleRing (𝓞 F) F), ?_, ?_⟩` and prove the remaining obligations. Introduce `D hD`.

Establish `hD' : IsCompact (h '' D)` using `hD.image h.continuous`. Use `((Set.Finite.pi (t := fun i => {x : F | algebraMap F (AdeleRing (𝓞 F) F) x ∈ (fun y => y i) '' (h '' D)}) fun i => finite_setOf_algebraMap_mem_of_isCompact F (hD'.image (continuous_apply i))).preimage b.equivFun.injective.injOn).subset ?_` and prove the remaining obligations. Introduce `β hβ`. Simplify using `only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq]`. Introduce `i`.

Conclude with `⟨h (_root_.Formalism.UG.inclE (AdeleRing (𝓞 F) F) β), ⟨_, hβ, rfl⟩, by rw [he]⟩`. Take `⟨K, hK, hKF⟩` from `_root_.GlobalTheory.AdeleCocompact.exists_compact_adele F`. Use `⟨h.symm '' Set.univ.pi fun _ => K, (isCompact_univ_pi fun _ => hK).image h.symm.continuous, fun x => ?_⟩` and prove the remaining obligations. Use `choose y hy using fun i => hKF (h x i)`. Use `⟨b.equivFun.symm y, h (x - _root_.Formalism.UG.inclE (AdeleRing (𝓞 F) F) (b.equivFun.symm y)), ?_, by simp⟩` and prove the remaining obligations.

Introduce `i _`. Rewrite using `[map_sub, he, LinearEquiv.apply_symm_apply]`. Simplify using `using hy i`.
-/
theorem _root_.GlobalTheory.RegSSLattice.tensorLattice : _root_.GlobalTheory.RegSS.TensorLattice := by
  unfold _root_.GlobalTheory.RegSS.TensorLattice
  intro F B _ _ _ _ _
  haveI := _root_.GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := _root_.GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := _root_.GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨U, hU, hUF⟩ := _root_.GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  haveI : Nontrivial (AdeleRing (𝓞 F) F) := ⟨⟨0, 1, fun h01 => one_ne_zero
    (hUF 1 (by rw [map_one, ← h01]; exact mem_of_mem_nhds hU))⟩⟩
  letI : Algebra (AdeleRing (𝓞 F) F) (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Algebra.TensorProduct.rightAlgebra
  letI : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) := _root_.Formalism.BasicNotions.tensTopL (AdeleRing (𝓞 F) F)
  haveI : IsModuleTopology (AdeleRing (𝓞 F) F) (B ⊗[F] AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : ContinuousAdd (B ⊗[F] AdeleRing (𝓞 F) F) :=
    IsModuleTopology.toContinuousAdd (AdeleRing (𝓞 F) F) _
  let b := Module.finBasis F B
  let c : B ⊗[F] AdeleRing (𝓞 F) F ≃ₗ[AdeleRing (𝓞 F) F] AdeleRing (𝓞 F) F ⊗[F] B :=
    { TensorProduct.comm F B (AdeleRing (𝓞 F) F) with
      map_smul' := fun a t => by
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul x y =>
          change TensorProduct.comm F B _ (a • (x ⊗ₜ y)) = a • TensorProduct.comm F B _ (x ⊗ₜ y)
          rw [Algebra.smul_def]
          simp [Algebra.TensorProduct.right_algebraMap_apply, TensorProduct.smul_tmul', mul_comm]
        | add x y hx hy => simp_all [smul_add] }
  let e := c.trans (Algebra.TensorProduct.basis (AdeleRing (𝓞 F) F) b).equivFun
  haveI : Module.Finite (AdeleRing (𝓞 F) F) (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Module.Finite.of_basis ((Algebra.TensorProduct.basis (AdeleRing (𝓞 F) F) b).map c.symm)
  let h : B ⊗[F] AdeleRing (𝓞 F) F ≃L[AdeleRing (𝓞 F) F]
      (Fin (Module.finrank F B) → AdeleRing (𝓞 F) F) :=
    { e with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  have he : ∀ β : B, h (_root_.Formalism.UG.inclE (AdeleRing (𝓞 F) F) β) =
      fun i => algebraMap F (AdeleRing (𝓞 F) F) (b.equivFun β i) := by
    intro β
    ext i
    show e (β ⊗ₜ 1) i = _
    simp [e, c, Algebra.TensorProduct.basis_repr_tmul]
  refine ⟨IsModuleTopology.isTopologicalRing (AdeleRing (𝓞 F) F) _,
    h.toHomeomorph.isClosedEmbedding.locallyCompactSpace, h.toHomeomorph.isEmbedding.t2Space,
    h.toHomeomorph.secondCountableTopology, _root_.Formalism.UG.P.inclE_injective F B (AdeleRing (𝓞 F) F), ?_, ?_⟩
  · intro D hD
    have hD' : IsCompact (h '' D) := hD.image h.continuous
    refine ((Set.Finite.pi (t := fun i => {x : F | algebraMap F (AdeleRing (𝓞 F) F) x ∈
      (fun y => y i) '' (h '' D)}) fun i => finite_setOf_algebraMap_mem_of_isCompact F
        (hD'.image (continuous_apply i))).preimage b.equivFun.injective.injOn).subset ?_
    intro β hβ
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq]
    intro i
    exact ⟨h (_root_.Formalism.UG.inclE (AdeleRing (𝓞 F) F) β), ⟨_, hβ, rfl⟩, by rw [he]⟩
  · obtain ⟨K, hK, hKF⟩ := _root_.GlobalTheory.AdeleCocompact.exists_compact_adele F
    refine ⟨h.symm '' Set.univ.pi fun _ => K,
      (isCompact_univ_pi fun _ => hK).image h.symm.continuous, fun x => ?_⟩
    choose y hy using fun i => hKF (h x i)
    refine ⟨b.equivFun.symm y, h (x - _root_.Formalism.UG.inclE (AdeleRing (𝓞 F) F) (b.equivFun.symm y)), ?_,
      by simp⟩
    intro i _
    rw [map_sub, he, LinearEquiv.apply_symm_apply]
    simpa using hy i

end GlobalTheory.RegSSLattice
