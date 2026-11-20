import Mathlib
import GroundTheory.GlobalFields.GlobalArtinMap.ArtinMap
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
import GroundTheory.GlobalFields.ClassFieldConsequences.OpenSubgroup

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField IdeleGroup GroundTheory.LocalField

noncomputable section

universe u

instance IdeleClassGroup.normal_connectedComponentOfOne (K : Type*) [Field K] [NumberField K] :
    (Subgroup.connectedComponentOfOne (IdeleClassGroup K)).Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩

section Path

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Break down `w.isReal_or_isComplex with hw | hw` into its components or cases. Set `u : ℝ → ℝˣ` to `fun t ↦ Units.mk0 (Real.exp t) (Real.exp_ne_zero t)`. Establish `hu : Continuous u` using `Units.isEmbedding_val₀.isInducing.continuous_iff.2 Real.continuous_exp`. Establish `hu0 : u 0 = 1` using `Units.ext (by simp [u])`. Use `⟨fun t ↦ infiniteEmbedding w (realUnitsHom hw (u t)), (continuous_infiniteEmbedding w).comp ((realUnitsHom hw).continuous.comp hu), ?_, fun t ↦ ?_⟩` and prove the remaining obligations.

Simplify using `only [hu0, map_one]`. Rewrite using `[ideleModule_infiniteEmbedding]`. Set `e` to `InfinitePlace.Completion.ringEquivRealOfIsReal hw`. Establish `hval : ((realUnitsHom hw (u t) : (w.Completion)ˣ) : w.Completion) = e.symm (Real.exp t)`. Both sides reduce to the same expression.

Establish `hn : ‖e.symm (Real.exp t)‖ = ‖e (e.symm (Real.exp t))‖`. Rewrite using `[InfinitePlace.Completion.ringEquivRealOfIsReal_apply]`. Conclude with `((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _).symm`. Rewrite using `[hval, hn, RingEquiv.apply_symm_apply, Real.norm_of_nonneg (Real.exp_pos t).le]`. Simplify using `[InfinitePlace.mult, hw]`.

Set `u : ℝ → ℂˣ` to `fun t ↦ Units.mk0 ((Real.exp (t / 2) : ℝ) : ℂ) (Complex.ofReal_ne_zero.2 (Real.exp_ne_zero _))`. Establish `hu : Continuous u` using `Units.isEmbedding_val₀.isInducing.continuous_iff.2 (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.div_const 2)))`. Establish `hu0 : u 0 = 1` using `Units.ext (by simp [u])`. Use `⟨fun t ↦ infiniteEmbedding w (complexUnitsHom hw (u t)), (continuous_infiniteEmbedding w).comp ((complexUnitsHom hw).continuous.comp hu), ?_, fun t ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [hu0, map_one]`.

Rewrite using `[ideleModule_infiniteEmbedding]`. Set `e` to `InfinitePlace.Completion.ringEquivComplexOfIsComplex hw`. Establish `hval : ((complexUnitsHom hw (u t) : (w.Completion)ˣ) : w.Completion) = e.symm ((Real.exp (t / 2) : ℝ) : ℂ)`. Both sides reduce to the same expression. Establish `hn : ‖e.symm ((Real.exp (t / 2) : ℝ) : ℂ)‖ = ‖e (e.symm ((Real.exp (t / 2) : ℝ) : ℂ))‖`.

Rewrite using `[InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]`. Conclude with `((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm`. Establish `hw' : ¬ w.IsReal` using `InfinitePlace.not_isReal_iff_isComplex.2 hw`. Rewrite using `[hval, hn, RingEquiv.apply_symm_apply, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]`. Simplify using `only [InfinitePlace.mult, hw', if_false]`.

Rewrite using `[sq, ← Real.exp_add, add_halves]`.
-/
theorem IdeleGroup.exists_continuous_ideleModule_eq_exp (w : InfinitePlace K) :
    ∃ γ : ℝ → IdeleGroup K, Continuous γ ∧ γ 0 = 1 ∧
      ∀ t, (IdeleGroup.ideleModule K (γ t) : ℝ) = Real.exp t := by
  rcases w.isReal_or_isComplex with hw | hw
  · let u : ℝ → ℝˣ := fun t ↦ Units.mk0 (Real.exp t) (Real.exp_ne_zero t)
    have hu : Continuous u := Units.isEmbedding_val₀.isInducing.continuous_iff.2 Real.continuous_exp
    have hu0 : u 0 = 1 := Units.ext (by simp [u])
    refine ⟨fun t ↦ infiniteEmbedding w (realUnitsHom hw (u t)),
      (continuous_infiniteEmbedding w).comp ((realUnitsHom hw).continuous.comp hu), ?_, fun t ↦ ?_⟩
    · simp only [hu0, map_one]
    · rw [ideleModule_infiniteEmbedding]
      let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
      have hval : ((realUnitsHom hw (u t) : (w.Completion)ˣ) : w.Completion) = e.symm (Real.exp t) :=
        rfl
      have hn : ‖e.symm (Real.exp t)‖ = ‖e (e.symm (Real.exp t))‖ := by
        rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
        exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
          (map_zero _) _).symm
      rw [hval, hn, RingEquiv.apply_symm_apply, Real.norm_of_nonneg (Real.exp_pos t).le]
      simp [InfinitePlace.mult, hw]
  · let u : ℝ → ℂˣ := fun t ↦ Units.mk0 ((Real.exp (t / 2) : ℝ) : ℂ)
      (Complex.ofReal_ne_zero.2 (Real.exp_ne_zero _))
    have hu : Continuous u := Units.isEmbedding_val₀.isInducing.continuous_iff.2
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.div_const 2)))
    have hu0 : u 0 = 1 := Units.ext (by simp [u])
    refine ⟨fun t ↦ infiniteEmbedding w (complexUnitsHom hw (u t)),
      (continuous_infiniteEmbedding w).comp ((complexUnitsHom hw).continuous.comp hu), ?_, fun t ↦ ?_⟩
    · simp only [hu0, map_one]
    · rw [ideleModule_infiniteEmbedding]
      let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      have hval : ((complexUnitsHom hw (u t) : (w.Completion)ˣ) : w.Completion) =
          e.symm ((Real.exp (t / 2) : ℝ) : ℂ) :=
        rfl
      have hn : ‖e.symm ((Real.exp (t / 2) : ℝ) : ℂ)‖ = ‖e (e.symm ((Real.exp (t / 2) : ℝ) : ℂ))‖ := by
        rw [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
        exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) _).symm
      have hw' : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hw
      rw [hval, hn, RingEquiv.apply_symm_apply, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      simp only [InfinitePlace.mult, hw', if_false]
      rw [sq, ← Real.exp_add, add_halves]

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace K)` from `inferInstance`. Take `⟨γ, hγc, hγ0, hγm⟩` from `IdeleGroup.exists_continuous_ideleModule_eq_exp w`. Use `set t := Real.log (IdeleClassGroup.ideleModule K c : ℝ)`. Use `set e := IdeleClassGroup.mk K (γ t)`. Establish `he : IdeleClassGroup.ideleModule K e = IdeleClassGroup.ideleModule K c`.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(IdeleGroup.ideleModule K (γ t) : ℝ) = _`. Rewrite using `[hγm, Real.exp_log (IdeleClassGroup.ideleModule K c).2]`. Use `⟨c * e⁻¹, ?_, e, ?_, (inv_mul_cancel_right c e).symm⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IdeleClassGroup.ideleModule K (c * e⁻¹) = 1`.

Rewrite using `[map_mul, map_inv, he, mul_inv_cancel]`. Use `(isPreconnected_range ((IdeleClassGroup.continuous_mk K).comp hγc)).subset_connectedComponent ⟨0, ?_⟩ ⟨t, rfl⟩` and prove the remaining obligations. Simplify using `only [Function.comp_apply, hγ0, map_one]`.
-/
theorem IdeleClassGroup.exists_mem_normOneSubgroup_mul_eq (c : IdeleClassGroup K) :
    ∃ d ∈ IdeleClassGroup.normOneSubgroup K, ∃ e ∈ connectedComponent (1 : IdeleClassGroup K),
      c = d * e := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  obtain ⟨γ, hγc, hγ0, hγm⟩ := IdeleGroup.exists_continuous_ideleModule_eq_exp w
  set t := Real.log (IdeleClassGroup.ideleModule K c : ℝ)
  set e := IdeleClassGroup.mk K (γ t)
  have he : IdeleClassGroup.ideleModule K e = IdeleClassGroup.ideleModule K c := by
    apply Subtype.ext
    change (IdeleGroup.ideleModule K (γ t) : ℝ) = _
    rw [hγm, Real.exp_log (IdeleClassGroup.ideleModule K c).2]
  refine ⟨c * e⁻¹, ?_, e, ?_, (inv_mul_cancel_right c e).symm⟩
  · change IdeleClassGroup.ideleModule K (c * e⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  · refine (isPreconnected_range ((IdeleClassGroup.continuous_mk K).comp hγc)).subset_connectedComponent
      ⟨0, ?_⟩ ⟨t, rfl⟩
    simp only [Function.comp_apply, hγ0, map_one]

end Path

section Surjective

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/- English proof (translation)
The claim follows from `fun c hc ↦ ext_restrictAb fun L _ _ ↦ by rw [restrictAb_artinMap, map_one] have hopen : IsOpen ((reciprocityMap K L).ker : Set (IdeleClassGroup K)) := by rw [MonoidHom.coe_ker] exact (isOpen_discrete _).preimage continuous_reciprocityMap exact Subgroup.subset_of_isPreconnected _ …`.
-/
theorem connectedComponent_subset_ker_artinMap :
    connectedComponent (1 : IdeleClassGroup K) ⊆ (artinMap K Ω).ker := fun c hc ↦
  ext_restrictAb fun L _ _ ↦ by
    rw [restrictAb_artinMap, map_one]
    have hopen : IsOpen ((reciprocityMap K L).ker : Set (IdeleClassGroup K)) := by
      rw [MonoidHom.coe_ker]
      exact (isOpen_discrete _).preimage continuous_reciprocityMap
    exact Subgroup.subset_of_isPreconnected _ hopen isPreconnected_connectedComponent
      mem_connectedComponent hc

/- English proof (translation)
Take `⟨d, hd, e, he, rfl⟩` from `IdeleClassGroup.exists_mem_normOneSubgroup_mul_eq c`. Use `⟨d, hd, ?_⟩` and prove the remaining obligations. Establish `h` using `connectedComponent_subset_ker_artinMap (Ω := Ω) he`. Rewrite `h` using `[SetLike.mem_coe, MonoidHom.mem_ker]`. Rewrite using `[map_mul, h, mul_one]`.
-/
theorem exists_mem_normOneSubgroup_artinMap_eq (c : IdeleClassGroup K) :
    ∃ d ∈ IdeleClassGroup.normOneSubgroup K, artinMap K Ω d = artinMap K Ω c := by
  obtain ⟨d, hd, e, he, rfl⟩ := IdeleClassGroup.exists_mem_normOneSubgroup_mul_eq c
  refine ⟨d, hd, ?_⟩
  have h := connectedComponent_subset_ker_artinMap (Ω := Ω) he
  rw [SetLike.mem_coe, MonoidHom.mem_ker] at h
  rw [map_mul, h, mul_one]

/- English proof (translation)
Introduce `τ`. Set `N` to `IdeleClassGroup.normOneSubgroup K`. Set `f : N → (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω)` to `fun d ↦ artinMap K Ω d`. Establish `hf : Continuous f` using `continuous_artinMap.comp continuous_subtype_val`. Set `t : finiteAbelianExtensions K Ω → Set N` to `fun L ↦`.

Use `L.2.1` as an intermediate fact. Use `L.2.2` as an intermediate fact. Use the proof step `{d | restrictAb (L : IntermediateField K Ω) (le_maximalAbelianExtension _) (f d) = restrictAb (L : IntermediateField K Ω) (le_maximalAbelianExtension _) τ}`. Establish `hcl : ∀ L, IsClosed (t L)` using `fun L ↦ by`. Use `L.2.1` as an intermediate fact.

Use `L.2.2` as an intermediate fact. Conclude with `isClosed_eq ((continuous_restrictAb _ _).comp hf) continuous_const`. Establish `hne : ∀ L, (t L).Nonempty` using `fun L ↦ by`. Use `L.2.1` as an intermediate fact. Use `L.2.2` as an intermediate fact.

Take `⟨c, hc⟩` from `reciprocityMap_surjective (K := K) (L := (L : IntermediateField K Ω)) (restrictAb (L : IntermediateField K Ω) (le_maximalAbelianExtension _) τ)`. Take `⟨d, hd, hdc⟩` from `exists_mem_normOneSubgroup_artinMap_eq (Ω := Ω) c`. Use `⟨⟨d, hd⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `restrictAb _ _ (artinMap K Ω d) = _`. Rewrite using `[hdc, restrictAb_artinMap, hc]`.

Establish `hdir : Directed (· ⊇ ·) t`. Introduce `L₁ L₂`. Use `L₁.2.1` as an intermediate fact. Use `L₁.2.2` as an intermediate fact. Use `L₂.2.1` as an intermediate fact.

Use `L₂.2.2` as an intermediate fact. Use `⟨⟨(L₁ : IntermediateField K Ω) ⊔ L₂, inferInstance, inferInstance⟩, fun d hd ↦ ?_, fun d hd ↦ ?_⟩` and prove the remaining obligations. Conclude with `restrictAb_eq_of_le (le_maximalAbelianExtension _) le_sup_left hd`. Conclude with `restrictAb_eq_of_le (le_maximalAbelianExtension _) le_sup_right hd`. Take `⟨d, hd⟩` from `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne (fun L ↦ (hcl L).isCompact) hcl`.

Use `⟨d, ext_restrictAb fun L _ _ ↦ ?_⟩` and prove the remaining obligations. Conclude with `Set.mem_iInter.1 hd ⟨L, inferInstance, inferInstance⟩`.
-/
theorem artinMap_surjective : Function.Surjective (artinMap K Ω) := by
  intro τ
  let N := IdeleClassGroup.normOneSubgroup K
  let f : N → (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :=
    fun d ↦ artinMap K Ω d
  have hf : Continuous f := continuous_artinMap.comp continuous_subtype_val
  let t : finiteAbelianExtensions K Ω → Set N := fun L ↦
    have := L.2.1
    have := L.2.2
    {d | restrictAb (L : IntermediateField K Ω) (le_maximalAbelianExtension _) (f d) =
      restrictAb (L : IntermediateField K Ω) (le_maximalAbelianExtension _) τ}
  have hcl : ∀ L, IsClosed (t L) := fun L ↦ by
    have := L.2.1
    have := L.2.2
    exact isClosed_eq ((continuous_restrictAb _ _).comp hf) continuous_const
  have hne : ∀ L, (t L).Nonempty := fun L ↦ by
    have := L.2.1
    have := L.2.2
    obtain ⟨c, hc⟩ := reciprocityMap_surjective (K := K) (L := (L : IntermediateField K Ω))
      (restrictAb (L : IntermediateField K Ω) (le_maximalAbelianExtension _) τ)
    obtain ⟨d, hd, hdc⟩ := exists_mem_normOneSubgroup_artinMap_eq (Ω := Ω) c
    refine ⟨⟨d, hd⟩, ?_⟩
    change restrictAb _ _ (artinMap K Ω d) = _
    rw [hdc, restrictAb_artinMap, hc]
  have hdir : Directed (· ⊇ ·) t := by
    intro L₁ L₂
    have := L₁.2.1
    have := L₁.2.2
    have := L₂.2.1
    have := L₂.2.2
    refine ⟨⟨(L₁ : IntermediateField K Ω) ⊔ L₂, inferInstance, inferInstance⟩, fun d hd ↦ ?_,
      fun d hd ↦ ?_⟩
    · exact restrictAb_eq_of_le (le_maximalAbelianExtension _) le_sup_left hd
    · exact restrictAb_eq_of_le (le_maximalAbelianExtension _) le_sup_right hd
  obtain ⟨d, hd⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne
    (fun L ↦ (hcl L).isCompact) hcl
  refine ⟨d, ext_restrictAb fun L _ _ ↦ ?_⟩
  exact Set.mem_iInter.1 hd ⟨L, inferInstance, inferInstance⟩

end Surjective

section Kernel

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω]

/- English proof (translation)
Take `⟨a, rfl⟩` from `QuotientGroup.mk_surjective y`. Establish `h : (QuotientGroup.mk : IdeleClassGroup K → IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K)) ⁻¹' {(a : IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K))} = (fun x ↦ a * x) '' connectedComponent (1 : IdeleClassGroup K)`. Use extensionality with `x`. Rewrite using `[Set.image_mul_left, Set.mem_preimage, Set.mem_preimage, Set.mem_singleton_iff, eq_comm, QuotientGroup.eq]`. Both sides reduce to the same expression.

Rewrite using `[h]`. Conclude with `isConnected_connectedComponent.image _ (continuous_const_mul a).continuousOn`.
-/
theorem IdeleClassGroup.isConnected_preimage_mk_connectedComponent
    (y : IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K)) :
    IsConnected ((QuotientGroup.mk : IdeleClassGroup K →
      IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K)) ⁻¹' {y}) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
  have h : (QuotientGroup.mk : IdeleClassGroup K →
      IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K)) ⁻¹'
        {(a : IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K))} =
      (fun x ↦ a * x) '' connectedComponent (1 : IdeleClassGroup K) := by
    ext x
    rw [Set.image_mul_left, Set.mem_preimage, Set.mem_preimage, Set.mem_singleton_iff, eq_comm,
      QuotientGroup.eq]
    rfl
  rw [h]
  exact isConnected_connectedComponent.image _ (continuous_const_mul a).continuousOn

/- English proof (translation)
Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed K`. Use `le_antisymm (fun c hc ↦ ?_) fun c hc ↦ connectedComponent_subset_ker_artinMap hc` and prove the remaining obligations. Assume the negation of the conclusion as `hcD`. Use `set D := Subgroup.connectedComponentOfOne (IdeleClassGroup K)`. Establish `hDcl : IsClosed (D : Set (IdeleClassGroup K))` using `isClosed_connectedComponent`.

Set `π : IdeleClassGroup K → IdeleClassGroup K ⧸ D` to `QuotientGroup.mk`. Establish `hπc : Continuous π` using `continuous_quotient_mk'`. Establish `himage : π '' (IdeleClassGroup.normOneSubgroup K : Set (IdeleClassGroup K)) = Set.univ`. Use `Set.eq_univ_of_forall fun q ↦ ?_` and prove the remaining obligations. Take `⟨c', rfl⟩` from `QuotientGroup.mk_surjective q`.

Take `⟨d, hd, e, he, rfl⟩` from `IdeleClassGroup.exists_mem_normOneSubgroup_mul_eq c'`. Use `⟨d, hd, QuotientGroup.eq.2 ?_⟩` and prove the remaining obligations. Conclude with `(inv_mul_cancel_left d e).symm ▸ he`. Establish `: CompactSpace (IdeleClassGroup K ⧸ D)` using `⟨himage ▸ (IdeleClassGroup.isCompact_normOneSubgroup K).image hπc⟩`. Establish `hpre` using `(QuotientGroup.isQuotientMap_mk D).isCoinducing.preimage_connectedComponent IdeleClassGroup.isConnected_preimage_mk_connectedComponent 1`.

Establish `hnot : π c ∉ connectedComponent (π 1)`. Introduce `h`. Establish `h' : c ∈ π ⁻¹' connectedComponent (π 1)` using `h`. Rewrite `h'` using `[hpre]`. Conclude with `hcD h'`.

Rewrite `hnot` using `[connectedComponent_eq_iInter_isClopen, Set.mem_iInter]`. Use `push Not at hnot`. Take `⟨⟨W, hWc, hW1⟩, hcW⟩` from `hnot`. Use `replace hW1 : (1 : IdeleClassGroup K ⧸ D) ∈ W := hW1`. Take `⟨H, hHW⟩` from `IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hWc hW1`.

Set `N : Subgroup (IdeleClassGroup K)` to `(H : Subgroup (IdeleClassGroup K ⧸ D)).comap (QuotientGroup.mk' D)`. Establish `hNopen : IsOpen (N : Set (IdeleClassGroup K))` using `H.isOpen.preimage hπc`. Establish `: (H : Subgroup (IdeleClassGroup K ⧸ D)).FiniteIndex` using `Subgroup.finiteIndex_of_finite_quotient`. Establish `: N.FiniteIndex` using `⟨by`. Rewrite using `[Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective D)]`.

Conclude with `Subgroup.FiniteIndex.index_ne_zero⟩`. Establish `hcN : c ∉ N` using `fun h ↦ hcW (hHW h)`. Take `⟨L, _, _, hL⟩` from `exists_intermediateField_range_ideleClassNorm_eq_of_finiteIndex (Ω := Ω) N hNopen`. Apply `hcN` to reduce the goal to its premises. Rewrite using `[← hL, ← ker_reciprocityMap, MonoidHom.mem_ker, ← restrictAb_artinMap L c, MonoidHom.mem_ker.1 hc, map_one]`.
-/
theorem ker_artinMap :
    (artinMap K Ω).ker = Subgroup.connectedComponentOfOne (IdeleClassGroup K) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  refine le_antisymm (fun c hc ↦ ?_) fun c hc ↦ connectedComponent_subset_ker_artinMap hc
  by_contra hcD
  set D := Subgroup.connectedComponentOfOne (IdeleClassGroup K)
  have hDcl : IsClosed (D : Set (IdeleClassGroup K)) := isClosed_connectedComponent
  let π : IdeleClassGroup K → IdeleClassGroup K ⧸ D := QuotientGroup.mk
  have hπc : Continuous π := continuous_quotient_mk'

  have himage : π '' (IdeleClassGroup.normOneSubgroup K : Set (IdeleClassGroup K)) = Set.univ := by
    refine Set.eq_univ_of_forall fun q ↦ ?_
    obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨d, hd, e, he, rfl⟩ := IdeleClassGroup.exists_mem_normOneSubgroup_mul_eq c'
    refine ⟨d, hd, QuotientGroup.eq.2 ?_⟩
    exact (inv_mul_cancel_left d e).symm ▸ he
  have : CompactSpace (IdeleClassGroup K ⧸ D) :=
    ⟨himage ▸ (IdeleClassGroup.isCompact_normOneSubgroup K).image hπc⟩

  have hpre := (QuotientGroup.isQuotientMap_mk D).isCoinducing.preimage_connectedComponent
    IdeleClassGroup.isConnected_preimage_mk_connectedComponent 1
  have hnot : π c ∉ connectedComponent (π 1) := by
    intro h
    have h' : c ∈ π ⁻¹' connectedComponent (π 1) := h
    rw [hpre] at h'
    exact hcD h'
  rw [connectedComponent_eq_iInter_isClopen, Set.mem_iInter] at hnot
  push Not at hnot
  obtain ⟨⟨W, hWc, hW1⟩, hcW⟩ := hnot
  replace hW1 : (1 : IdeleClassGroup K ⧸ D) ∈ W := hW1
  obtain ⟨H, hHW⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hWc hW1

  let N : Subgroup (IdeleClassGroup K) := (H : Subgroup (IdeleClassGroup K ⧸ D)).comap (QuotientGroup.mk' D)
  have hNopen : IsOpen (N : Set (IdeleClassGroup K)) := H.isOpen.preimage hπc
  have : (H : Subgroup (IdeleClassGroup K ⧸ D)).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  have : N.FiniteIndex := ⟨by
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective D)]
    exact Subgroup.FiniteIndex.index_ne_zero⟩
  have hcN : c ∉ N := fun h ↦ hcW (hHW h)

  obtain ⟨L, _, _, hL⟩ := exists_intermediateField_range_ideleClassNorm_eq_of_finiteIndex (Ω := Ω) N
    hNopen
  apply hcN
  rw [← hL, ← ker_reciprocityMap, MonoidHom.mem_ker, ← restrictAb_artinMap L c,
    MonoidHom.mem_ker.1 hc, map_one]

def artinQuotientEquiv :
    IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K) ≃ₜ*
      (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :=
  have : T2Space (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) := krullTopology_t2
  have hDcl : IsClosed ((Subgroup.connectedComponentOfOne (IdeleClassGroup K)) :
    Set (IdeleClassGroup K)) := isClosed_connectedComponent
  let e := (QuotientGroup.quotientMulEquivOfEq (ker_artinMap (K := K) (Ω := Ω)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ artinMap_surjective)
  have hc : Continuous e := by
    refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    have h : (e ∘ QuotientGroup.mk) = artinMap K Ω := funext fun _ ↦ rfl
    rw [h]
    exact continuous_artinMap
  have : CompactSpace (IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K)) := by
    refine ⟨?_⟩
    have himage : (QuotientGroup.mk : IdeleClassGroup K → IdeleClassGroup K ⧸
        Subgroup.connectedComponentOfOne (IdeleClassGroup K)) ''
          (IdeleClassGroup.normOneSubgroup K : Set (IdeleClassGroup K)) = Set.univ := by
      refine Set.eq_univ_of_forall fun q ↦ ?_
      obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨d, hd, e, he, rfl⟩ := IdeleClassGroup.exists_mem_normOneSubgroup_mul_eq c'
      refine ⟨d, hd, QuotientGroup.eq.2 ?_⟩
      exact (inv_mul_cancel_left d e).symm ▸ he
    exact himage ▸ (IdeleClassGroup.isCompact_normOneSubgroup K).image continuous_quotient_mk'
  { e with
    continuous_toFun := hc
    continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

end Kernel

end

end GroundTheory.Global
