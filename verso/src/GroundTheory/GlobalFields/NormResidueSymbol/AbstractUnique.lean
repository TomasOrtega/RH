import Mathlib
import GroundTheory.GlobalFields.NormResidueSymbol.Abstract

namespace GroundTheory.Global

open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

noncomputable section

namespace IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

def localEmbeddingSubgroup : Subgroup (IdeleGroup K) :=
  (⨆ v : HeightOneSpectrum (𝓞 K), (finiteEmbedding v).range) ⊔
    ⨆ w : InfinitePlace K, (infiniteEmbedding w).range

variable {K}

/- English proof (translation)
The claim follows from `Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem v ⟨a, rfl⟩)`.
-/
theorem finiteEmbedding_mem_localEmbeddingSubgroup (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) : finiteEmbedding v a ∈ localEmbeddingSubgroup K :=
  Subgroup.mem_sup_left (Subgroup.mem_iSup_of_mem v ⟨a, rfl⟩)

/- English proof (translation)
The claim follows from `Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem w ⟨a, rfl⟩)`.
-/
theorem infiniteEmbedding_mem_localEmbeddingSubgroup (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    infiniteEmbedding w a ∈ localEmbeddingSubgroup K :=
  Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem w ⟨a, rfl⟩)

/- English proof (translation)
Take `⟨_, ⟨U, V, -, -, hVO, rfl⟩, h1, htN⟩` from `(isTopologicalBasis K).mem_nhds_iff.1 hN`. Establish `hU1 : ∀ w, (1 : (w.Completion)ˣ) ∈ U w` using `fun w ↦ by simpa using h1.1 w`. Establish `hV1 : ∀ v, (1 : (v.adicCompletion K)ˣ) ∈ V v` using `fun v ↦ by simpa using h1.2 v`. Establish `hS : {v : HeightOneSpectrum (𝓞 K) | ¬ (V v = ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ) ∧ finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units)}.Finite` using `eventually_cofinite.1 (hVO.and (eventually_finiteProj_mem_units x))`. Use `set S := hS.toFinset with hSdef`.

Use `set h : IdeleGroup K := (∏ w, infiniteEmbedding w (infiniteProj w x)) * ∏ v ∈ S, finiteEmbedding v (finiteProj v x) with hhdef`. Use `⟨h, ?_, htN ⟨fun w ↦ ?_, fun v ↦ ?_⟩⟩` and prove the remaining obligations. Conclude with `Subgroup.mul_mem _ (Subgroup.prod_mem _ fun w _ ↦ infiniteEmbedding_mem_localEmbeddingSubgroup _ _) (Subgroup.prod_mem _ fun v _ ↦ finiteEmbedding_mem_localEmbeddingSubgroup _ _)`. Establish `hfi : ∀ (u : HeightOneSpectrum (𝓞 K)) (a : (u.adicCompletion K)ˣ), infiniteProj w (finiteEmbedding u a) = 1` using `fun _ _ ↦ Units.ext rfl`. Establish `hw : infiniteProj w h = infiniteProj w x`.

Simplify using `only [h, map_mul, map_prod, hfi, Finset.prod_const_one, mul_one]`. Rewrite using `[Finset.prod_eq_single w (fun u _ hu ↦ infiniteProj_infiniteEmbedding_of_ne (Ne.symm hu) _) (fun hw ↦ (hw (Finset.mem_univ w)).elim)]`. Simplify using the standard rewrite rules. Rewrite using `[map_mul, map_inv, hw, inv_mul_cancel]`. Conclude with `hU1 w`.

Establish `hif : ∀ (u : InfinitePlace K) (a : (u.Completion)ˣ), finiteProj v (infiniteEmbedding u a) = 1` using `fun _ _ ↦ Units.ext rfl`. Distinguish the cases in `hv : v ∈ S`. Establish `hv' : finiteProj v h = finiteProj v x`. Simplify using `only [h, map_mul, map_prod, hif, Finset.prod_const_one, one_mul]`. Rewrite using `[Finset.prod_eq_single_of_mem v hv (fun u _ hu ↦ finiteProj_finiteEmbedding_of_ne (Ne.symm hu) _)]`.

Simplify using the standard rewrite rules. Rewrite using `[map_mul, map_inv, hv', inv_mul_cancel]`. Conclude with `hV1 v`. Establish `hv' : finiteProj v h = 1`. Simplify using `only [h, map_mul, map_prod, hif, Finset.prod_const_one, one_mul]`.

Rewrite using `[Finset.prod_eq_one (fun u hu ↦ finiteProj_finiteEmbedding_of_ne (by rintro rfl; exact hv hu) _)]`. Establish `hvS` using `hv`. Rewrite `hvS` using `[hSdef, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not]`. Rewrite using `[map_mul, map_inv, hv', inv_one, one_mul, hvS.1]`. Conclude with `hvS.2`.
-/
theorem exists_mem_localEmbeddingSubgroup_inv_mul_mem {N : Set (IdeleGroup K)} (hN : N ∈ 𝓝 1)
    (x : IdeleGroup K) : ∃ h ∈ localEmbeddingSubgroup K, h⁻¹ * x ∈ N := by
  classical
  obtain ⟨_, ⟨U, V, -, -, hVO, rfl⟩, h1, htN⟩ := (isTopologicalBasis K).mem_nhds_iff.1 hN
  have hU1 : ∀ w, (1 : (w.Completion)ˣ) ∈ U w := fun w ↦ by simpa using h1.1 w
  have hV1 : ∀ v, (1 : (v.adicCompletion K)ˣ) ∈ V v := fun v ↦ by simpa using h1.2 v
  have hS : {v : HeightOneSpectrum (𝓞 K) | ¬ (V v =
      ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ) ∧
        finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units)}.Finite :=
    eventually_cofinite.1 (hVO.and (eventually_finiteProj_mem_units x))
  set S := hS.toFinset with hSdef
  set h : IdeleGroup K := (∏ w, infiniteEmbedding w (infiniteProj w x)) *
    ∏ v ∈ S, finiteEmbedding v (finiteProj v x) with hhdef
  refine ⟨h, ?_, htN ⟨fun w ↦ ?_, fun v ↦ ?_⟩⟩
  · exact Subgroup.mul_mem _
      (Subgroup.prod_mem _ fun w _ ↦ infiniteEmbedding_mem_localEmbeddingSubgroup _ _)
      (Subgroup.prod_mem _ fun v _ ↦ finiteEmbedding_mem_localEmbeddingSubgroup _ _)
  · have hfi : ∀ (u : HeightOneSpectrum (𝓞 K)) (a : (u.adicCompletion K)ˣ),
        infiniteProj w (finiteEmbedding u a) = 1 := fun _ _ ↦ Units.ext rfl
    have hw : infiniteProj w h = infiniteProj w x := by
      simp only [h, map_mul, map_prod, hfi, Finset.prod_const_one, mul_one]
      rw [Finset.prod_eq_single w
          (fun u _ hu ↦ infiniteProj_infiniteEmbedding_of_ne (Ne.symm hu) _)
          (fun hw ↦ (hw (Finset.mem_univ w)).elim)]
      simp
    rw [map_mul, map_inv, hw, inv_mul_cancel]
    exact hU1 w
  · have hif : ∀ (u : InfinitePlace K) (a : (u.Completion)ˣ),
        finiteProj v (infiniteEmbedding u a) = 1 := fun _ _ ↦ Units.ext rfl
    by_cases hv : v ∈ S
    · have hv' : finiteProj v h = finiteProj v x := by
        simp only [h, map_mul, map_prod, hif, Finset.prod_const_one, one_mul]
        rw [Finset.prod_eq_single_of_mem v hv
            (fun u _ hu ↦ finiteProj_finiteEmbedding_of_ne (Ne.symm hu) _)]
        simp
      rw [map_mul, map_inv, hv', inv_mul_cancel]
      exact hV1 v
    · have hv' : finiteProj v h = 1 := by
        simp only [h, map_mul, map_prod, hif, Finset.prod_const_one, one_mul]
        rw [Finset.prod_eq_one (fun u hu ↦ finiteProj_finiteEmbedding_of_ne
            (by rintro rfl; exact hv hu) _)]
      have hvS := hv
      rw [hSdef, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hvS
      rw [map_mul, map_inv, hv', inv_one, one_mul, hvS.1]
      exact hvS.2

/- English proof (translation)
Use `fun x ↦ mem_closure_iff_nhds.2 fun t ht ↦ ?_` and prove the remaining obligations. Establish `hN : {y : IdeleGroup K | x * y⁻¹ ∈ t} ∈ 𝓝 (1 : IdeleGroup K)`. Establish `hc : Continuous fun y : IdeleGroup K ↦ x * y⁻¹` using `continuous_const.mul continuous_inv`. Conclude with `hc.continuousAt.preimage_mem_nhds (by simpa using ht)`. Take `⟨h, hh, hhN⟩` from `exists_mem_localEmbeddingSubgroup_inv_mul_mem hN x`.

Conclude with `⟨h, by simpa using hhN, hh⟩`.
-/
theorem dense_localEmbeddingSubgroup : Dense (localEmbeddingSubgroup K : Set (IdeleGroup K)) := by
  refine fun x ↦ mem_closure_iff_nhds.2 fun t ht ↦ ?_
  have hN : {y : IdeleGroup K | x * y⁻¹ ∈ t} ∈ 𝓝 (1 : IdeleGroup K) := by
    have hc : Continuous fun y : IdeleGroup K ↦ x * y⁻¹ := continuous_const.mul continuous_inv
    exact hc.continuousAt.preimage_mem_nhds (by simpa using ht)
  obtain ⟨h, hh, hhN⟩ := exists_mem_localEmbeddingSubgroup_inv_mul_mem hN x
  exact ⟨h, by simpa using hhN, hh⟩

/- English proof (translation)
Establish `hle : localEmbeddingSubgroup K ≤ ψ.eqLocus ψ'` using `sup_le (iSup_le fun v ↦ by rintro _ ⟨a, rfl⟩; exact hfin v a) (iSup_le fun w ↦ by rintro _ ⟨a, rfl⟩; exact hinf w a)`. Conclude with `MonoidHom.ext (congrFun (Continuous.ext_on dense_localEmbeddingSubgroup hψ hψ' fun x hx ↦ hle hx))`.
-/
theorem continuous_monoidHom_ext {M : Type*} [Monoid M] [TopologicalSpace M] [T2Space M]
    {ψ ψ' : IdeleGroup K →* M} (hψ : Continuous ψ) (hψ' : Continuous ψ')
    (hfin : ∀ v a, ψ (finiteEmbedding v a) = ψ' (finiteEmbedding v a))
    (hinf : ∀ w a, ψ (infiniteEmbedding w a) = ψ' (infiniteEmbedding w a)) : ψ = ψ' := by
  have hle : localEmbeddingSubgroup K ≤ ψ.eqLocus ψ' :=
    sup_le (iSup_le fun v ↦ by rintro _ ⟨a, rfl⟩; exact hfin v a)
      (iSup_le fun w ↦ by rintro _ ⟨a, rfl⟩; exact hinf w a)
  exact MonoidHom.ext (congrFun (Continuous.ext_on dense_localEmbeddingSubgroup hψ hψ' fun x hx ↦ hle hx))

end IdeleGroup

namespace IdeleMap

open IdeleGroup

variable {K : Type*} [Field K] [NumberField K] {G : Type*} [CommGroup G]
  [TopologicalSpace G] [DiscreteTopology G]
  (φ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* G)
  (φinf : ∀ w : InfinitePlace K, (w.Completion)ˣ →* G)
  (hφ : ∀ᶠ v in cofinite,
    (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (φ v).ker)

/- English proof (translation)
The claim follows from `continuous_monoidHom_ext hψ (continuous_ideleMap φ φinf hφ hφc hφinfc) (fun v a ↦ by rw [ideleMap_finiteEmbedding, ← hfin v, MonoidHom.comp_apply]) (fun w a ↦ by rw [ideleMap_infiniteEmbedding, ← hinf w, MonoidHom.comp_apply])`.
-/
theorem eq_ideleMap (hφc : ∀ v, Continuous (φ v)) (hφinfc : ∀ w, Continuous (φinf w))
    {ψ : IdeleGroup K →* G} (hψ : Continuous ψ)
    (hfin : ∀ v, ψ.comp (finiteEmbedding v) = φ v)
    (hinf : ∀ w, ψ.comp (infiniteEmbedding w) = φinf w) :
    ψ = ideleMap φ φinf hφ :=
  continuous_monoidHom_ext hψ (continuous_ideleMap φ φinf hφ hφc hφinfc)
    (fun v a ↦ by rw [ideleMap_finiteEmbedding, ← hfin v, MonoidHom.comp_apply])
    (fun w a ↦ by rw [ideleMap_infiniteEmbedding, ← hinf w, MonoidHom.comp_apply])

include hφ in

/- English proof (translation)
Assemble the required witnesses or components as `⟨ideleMap φ φinf hφ, ⟨continuous_ideleMap φ φinf hφ hφc hφinfc, ideleMap_comp_finiteEmbedding φ φinf hφ, ideleMap_comp_infiniteEmbedding φ φinf hφ⟩, fun _ hψ ↦ eq_ideleMap φ φinf hφ hφc hφinfc hψ.1 hψ.2.1 hψ.2.2⟩`.
-/
theorem existsUnique_ideleMap (hφc : ∀ v, Continuous (φ v))
    (hφinfc : ∀ w, Continuous (φinf w)) :
    ∃! ψ : IdeleGroup K →* G, Continuous ψ ∧ (∀ v, ψ.comp (finiteEmbedding v) = φ v) ∧
      ∀ w, ψ.comp (infiniteEmbedding w) = φinf w :=
  ⟨ideleMap φ φinf hφ, ⟨continuous_ideleMap φ φinf hφ hφc hφinfc,
      ideleMap_comp_finiteEmbedding φ φinf hφ, ideleMap_comp_infiniteEmbedding φ φinf hφ⟩,
    fun _ hψ ↦ eq_ideleMap φ φinf hφ hφc hφinfc hψ.1 hψ.2.1 hψ.2.2⟩

end IdeleMap

end

end GroundTheory.Global
