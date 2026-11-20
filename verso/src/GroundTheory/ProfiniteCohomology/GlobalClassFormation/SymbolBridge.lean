import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalSymbol
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.IsScalarTowerFiniteSubfieldAlgebraicClosure
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.InfDefs
import GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global GroundTheory.Global.SemiLocal FiniteSubfield IsDedekindDomain

open scoped NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

attribute [local instance] FiniteSubfield.isGalois_of_normal

section Reciprocity

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]

/- English proof (translation)
Apply `(GroundTheory.LocalField.topologicalAbelianizationEquiv k (AlgebraicClosure k)).injective` to reduce the goal to its premises. Rewrite using `[GroundTheory.LocalField.topologicalAbelianizationEquiv_mk, ← GroundTheory.LocalField.localArtinMap_apply]`. Use `AlgEquiv.ext fun y ↦ Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[AlgEquiv.restrictNormalHom_apply]`. Conclude with `hg y y.2`.
-/
theorem mk_eq_localReciprocityLimit_of_forall {x : kˣ} {g : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k}
    (hg : ∀ (y : AlgebraicClosure k)
      (hy : y ∈ GroundTheory.LocalField.maximalAbelianExtension k (AlgebraicClosure k)),
      g y = (GroundTheory.LocalField.localArtinMap k (AlgebraicClosure k) x ⟨y, hy⟩ : AlgebraicClosure k)) :
    (g : TopologicalAbelianization (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) =
      GroundTheory.LocalField.localReciprocityLimit k (AlgebraicClosure k) x := by
  apply (GroundTheory.LocalField.topologicalAbelianizationEquiv k (AlgebraicClosure k)).injective
  rw [GroundTheory.LocalField.topologicalAbelianizationEquiv_mk, ← GroundTheory.LocalField.localArtinMap_apply]
  refine AlgEquiv.ext fun y ↦ Subtype.ext ?_
  rw [AlgEquiv.restrictNormalHom_apply]
  exact hg y y.2

end Reciprocity

variable {K : FiniteSubfield} (E : FiniteSubfield) [Fact (K ≤ E)]
  [(E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (E.1 ≃ₐ[K.1] E.1)]

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))

/- English proof (translation)
The claim follows from `normResidueSymbol_spec _ (mk_eq_localReciprocityLimit_of_forall hg) y`.
-/
theorem completionEmbedding_normResidueSymbol {b : (v.adicCompletion K.1)ˣ}
    {g : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)}
    (hg : ∀ (y : AlgebraicClosure (v.adicCompletion K.1))
      (hy : y ∈ GroundTheory.LocalField.maximalAbelianExtension (v.adicCompletion K.1)
        (AlgebraicClosure (v.adicCompletion K.1))),
      g y = (GroundTheory.LocalField.localArtinMap (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) b
        ⟨y, hy⟩ : AlgebraicClosure (v.adicCompletion K.1)))
    (y : (placeOfEmbedding ι E).1.adicCompletion E.1) :
    completionEmbedding ι E (normResidueSymbol (v.adicCompletion K.1) _ b y) =
      g (completionEmbedding ι E y) :=
  normResidueSymbol_spec _ (mk_eq_localReciprocityLimit_of_forall hg) y

/- English proof (translation)
Use `AlgEquiv.ext fun l ↦ Subtype.val_injective (ι.injective ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ι _ = ι _`. Rewrite using `[coe_restrictHom_apply, globalDecomp_apply, ← completionEmbedding_algebraMap ι E (localSymbol E.1 v b l), algebraMap_localSymbol_apply E.1 v (placeOfEmbedding ι E), completionEmbedding_normResidueSymbol E ι hg, completionEmbedding_algebraMap]`.
-/
theorem restrictHom_globalDecomp_of_finite {b : (v.adicCompletion K.1)ˣ}
    {g : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1)}
    (hg : ∀ (y : AlgebraicClosure (v.adicCompletion K.1))
      (hy : y ∈ GroundTheory.LocalField.maximalAbelianExtension (v.adicCompletion K.1)
        (AlgebraicClosure (v.adicCompletion K.1))),
      g y = (GroundTheory.LocalField.localArtinMap (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) b
        ⟨y, hy⟩ : AlgebraicClosure (v.adicCompletion K.1))) :
    restrictHom (E := E) (globalDecomp (v.adicCompletion K.1) ι g) = localSymbol E.1 v b := by
  refine AlgEquiv.ext fun l ↦ Subtype.val_injective (ι.injective ?_)
  change ι _ = ι _
  rw [coe_restrictHom_apply, globalDecomp_apply, ← completionEmbedding_algebraMap ι E (localSymbol E.1 v b l),
    algebraMap_localSymbol_apply E.1 v (placeOfEmbedding ι E), completionEmbedding_normResidueSymbol E ι hg,
    completionEmbedding_algebraMap]

end Finite

section Infinite

variable {v : InfinitePlace K.1} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)

omit [(E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (E.1 ≃ₐ[K.1] E.1)] in

/- English proof (translation)
Use `set w : InfinitePlace E.1 := (infPlaceOfEmbedding ι E : InfinitePlace E.1) with hw_def`. Use `set j := infCompletionEmbedding ι E with hj_def`. Use `set d := decompHom v.Completion j g with hd_def`. It suffices to establish `h : InfinitePlace.localSymbol v w b = d by`. Rewrite using `[h, hd_def]`.

Conclude with `decompHom_apply j g _`. Distinguish the cases in `h2 : v.IsReal ∧ w.IsComplex`. Take `⟨hv, hw⟩` from `h2`. Establish `hfin : Module.finrank v.Completion w.Completion = 2` using `(InfinitePlace.finrank_completion_eq_two_iff w).2 ⟨hv, hw⟩`. Establish `hinj : Function.Injective j.toLinearMap` using `j.injective`.

Establish `hsurj : Function.Surjective j`. Establish `hle` using `LinearMap.finrank_le_finrank_of_injective hinj`. Establish `heq : Module.finrank v.Completion w.Completion = Module.finrank v.Completion (AlgebraicClosure v.Completion)` using `le_antisymm hle (hfin ▸ infAlgClosure_finrank_le_two v)`. Conclude with `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hinj`. Set `e : w.Completion ≃ₐ[v.Completion] AlgebraicClosure v.Completion` to `AlgEquiv.ofBijective j ⟨j.injective, hsurj⟩`.

Establish `he : ∀ y, e y = j y` using `fun _ ↦ rfl`. Establish `hd : d = 1 ↔ g = 1`. Prove the components needed by the constructor for the conclusion. Introduce `hd1`. Use `AlgEquiv.ext fun z ↦ ?_` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `hsurj z`. Rewrite using `[← decompHom_apply, ← hd_def, hd1]`. Both sides reduce to the same expression. Introduce and unpack `rfl`. Conclude with `map_one _`.

Establish `hs : InfinitePlace.localSymbol v w b = 1 ↔ d = 1`. Rewrite using `[hd, hg, ← MonoidHom.mem_ker, InfinitePlace.ker_localSymbol, InfinitePlace.normSubgroup, MonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Use `⟨e y, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.norm_eq_of_algEquiv]`. Conclude with `congrArg Units.val hy`. Introduce and unpack `⟨z, hz⟩`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hz` using `[Algebra.norm_zero]`. Conclude with `b.ne_zero hz.symm`. Use `⟨Units.mk0 (e.symm z) ((map_ne_zero _).2 hz0), Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Units.coe_map, Units.val_mk0, ← Algebra.norm_eq_of_algEquiv e, e.apply_symm_apply, hz]`. Establish `hc` using `InfinitePlace.completionConj_ne_one (w := w) hv hw`.

Apply the tactic sequence `rcases InfinitePlace.eq_one_or_eq_completionConj hv hw (InfinitePlace.localSymbol v w b) with h1 | h1 <;>`. Break down `InfinitePlace.eq_one_or_eq_completionConj hv hw d with h3 | h3` into its components or cases. Rewrite using `[h1, h3]`. Conclude with `absurd (h3 ▸ hs.1 h1) hc`. Conclude with `absurd (h1 ▸ hs.2 h3) hc`.

Rewrite using `[h1, h3]`. Use `InfinitePlace.subsingleton_gal w h2` as an intermediate fact. Conclude with `Subsingleton.elim _ _`.
-/
theorem infCompletionEmbedding_localSymbol {b : v.Completionˣ}
    {g : Gal(AlgebraicClosure v.Completion/v.Completion)}
    (hg : g = 1 ↔ (b : v.Completion) ∈
      Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion))
    (y : (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) :
    infCompletionEmbedding ι E (InfinitePlace.localSymbol v (infPlaceOfEmbedding ι E : InfinitePlace E.1) b y) =
      g (infCompletionEmbedding ι E y) := by
  set w : InfinitePlace E.1 := (infPlaceOfEmbedding ι E : InfinitePlace E.1) with hw_def
  set j := infCompletionEmbedding ι E with hj_def
  set d := decompHom v.Completion j g with hd_def
  suffices h : InfinitePlace.localSymbol v w b = d by
    rw [h, hd_def]
    exact decompHom_apply j g _
  by_cases h2 : v.IsReal ∧ w.IsComplex
  · obtain ⟨hv, hw⟩ := h2
    have hfin : Module.finrank v.Completion w.Completion = 2 :=
      (InfinitePlace.finrank_completion_eq_two_iff w).2 ⟨hv, hw⟩
    have hinj : Function.Injective j.toLinearMap := j.injective
    have hsurj : Function.Surjective j := by
      have hle := LinearMap.finrank_le_finrank_of_injective hinj
      have heq : Module.finrank v.Completion w.Completion =
          Module.finrank v.Completion (AlgebraicClosure v.Completion) :=
        le_antisymm hle (hfin ▸ infAlgClosure_finrank_le_two v)
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hinj
    let e : w.Completion ≃ₐ[v.Completion] AlgebraicClosure v.Completion :=
      AlgEquiv.ofBijective j ⟨j.injective, hsurj⟩
    have he : ∀ y, e y = j y := fun _ ↦ rfl
    have hd : d = 1 ↔ g = 1 := by
      constructor
      · intro hd1
        refine AlgEquiv.ext fun z ↦ ?_
        obtain ⟨y, rfl⟩ := hsurj z
        rw [← decompHom_apply, ← hd_def, hd1]
        rfl
      · rintro rfl
        exact map_one _
    have hs : InfinitePlace.localSymbol v w b = 1 ↔ d = 1 := by
      rw [hd, hg, ← MonoidHom.mem_ker, InfinitePlace.ker_localSymbol, InfinitePlace.normSubgroup,
        MonoidHom.mem_range]
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨e y, ?_⟩
        rw [Algebra.norm_eq_of_algEquiv]
        exact congrArg Units.val hy
      · rintro ⟨z, hz⟩
        have hz0 : z ≠ 0 := by
          rintro rfl
          rw [Algebra.norm_zero] at hz
          exact b.ne_zero hz.symm
        refine ⟨Units.mk0 (e.symm z) ((map_ne_zero _).2 hz0), Units.ext ?_⟩
        rw [Units.coe_map, Units.val_mk0, ← Algebra.norm_eq_of_algEquiv e,
          e.apply_symm_apply, hz]
    have hc := InfinitePlace.completionConj_ne_one (w := w) hv hw
    rcases InfinitePlace.eq_one_or_eq_completionConj hv hw (InfinitePlace.localSymbol v w b) with h1 | h1 <;>
      rcases InfinitePlace.eq_one_or_eq_completionConj hv hw d with h3 | h3
    · rw [h1, h3]
    · exact absurd (h3 ▸ hs.1 h1) hc
    · exact absurd (h1 ▸ hs.2 h3) hc
    · rw [h1, h3]
  · have := InfinitePlace.subsingleton_gal w h2
    exact Subsingleton.elim _ _

/- English proof (translation)
Use `AlgEquiv.ext fun l ↦ Subtype.val_injective (ι.injective ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ι _ = ι _`. Rewrite using `[coe_restrictHom_apply, globalDecomp_apply, ← infCompletionEmbedding_algebraMap ι E (infiniteLocalSymbol E.1 v b l), algebraMap_infiniteLocalSymbol_apply E.1 v (infPlaceOfEmbedding ι E), infCompletionEmbedding_localSymbol E ι hg, infCompletionEmbedding_algebraMap]`.
-/
theorem restrictHom_globalDecomp_of_infinite {b : v.Completionˣ}
    {g : Gal(AlgebraicClosure v.Completion/v.Completion)}
    (hg : g = 1 ↔ (b : v.Completion) ∈
      Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion)) :
    restrictHom (E := E) (globalDecomp v.Completion ι g) = infiniteLocalSymbol E.1 v b := by
  refine AlgEquiv.ext fun l ↦ Subtype.val_injective (ι.injective ?_)
  change ι _ = ι _
  rw [coe_restrictHom_apply, globalDecomp_apply,
    ← infCompletionEmbedding_algebraMap ι E (infiniteLocalSymbol E.1 v b l),
    algebraMap_infiniteLocalSymbol_apply E.1 v (infPlaceOfEmbedding ι E),
    infCompletionEmbedding_localSymbol E ι hg, infCompletionEmbedding_algebraMap]

end Infinite

end

end GroundTheory.ProfCoh
