import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace GlobalTheory

section Abstract

variable {U T Z Y : Scheme.{u}}

/- English proof (translation)
Establish `hfac : j = pullback.lift a j h ≫ pullback.snd p b` using `(pullback.lift_snd _ _ _).symm`. Use `set d := j.normalizationDesc (pullback.lift a j h) (pullback.snd p b) hfac with hd`. Establish `e1 : j ≫ inv j.fromNormalization = j.toNormalization`. Rewrite using `[IsIso.comp_inv_eq, Scheme.Hom.toNormalization_fromNormalization]`. Use `⟨inv j.fromNormalization ≫ d ≫ pullback.fst p b, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Category.assoc, e1, hd, Scheme.Hom.toNormalization_normalizationDesc_assoc]`. Conclude with `pullback.lift_fst _ _ _`. Rewrite using `[Category.assoc, Category.assoc, pullback.condition, hd, Scheme.Hom.normalizationDesc_comp_assoc, IsIso.inv_hom_id_assoc]`. Introduce and unpack `c ⟨hc₁, hc₂⟩`. Establish `hl : c ≫ p = 𝟙 T ≫ b` using `by rw [hc₂, Category.id_comp]`.

Establish `key : j.fromNormalization ≫ pullback.lift c (𝟙 T) hl = d`. Apply `Scheme.Hom.normalization.hom_ext j _ _ (pullback.snd p b)` to reduce the goal to its premises. Rewrite using `[Scheme.Hom.toNormalization_fromNormalization_assoc, hd, Scheme.Hom.toNormalization_normalizationDesc]`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, pullback.lift_fst, pullback.lift_fst, hc₁]`.

Rewrite using `[Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]`. Rewrite using `[Category.assoc, pullback.lift_snd, Category.comp_id]`. Rewrite using `[hd, Scheme.Hom.normalizationDesc_comp]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem existsUnique_lift_of_isIso_fromNormalization (j : U ⟶ T) [QuasiCompact j]
    [QuasiSeparated j] [IsIso j.fromNormalization] (p : Z ⟶ Y) [IsIntegralHom p]
    (a : U ⟶ Z) (b : T ⟶ Y) (h : a ≫ p = j ≫ b) :
    ∃! c : T ⟶ Z, j ≫ c = a ∧ c ≫ p = b := by
  have hfac : j = pullback.lift a j h ≫ pullback.snd p b := (pullback.lift_snd _ _ _).symm
  set d := j.normalizationDesc (pullback.lift a j h) (pullback.snd p b) hfac with hd
  have e1 : j ≫ inv j.fromNormalization = j.toNormalization := by
    rw [IsIso.comp_inv_eq, Scheme.Hom.toNormalization_fromNormalization]
  refine ⟨inv j.fromNormalization ≫ d ≫ pullback.fst p b, ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, e1, hd, Scheme.Hom.toNormalization_normalizationDesc_assoc]
    exact pullback.lift_fst _ _ _
  · rw [Category.assoc, Category.assoc, pullback.condition, hd,
      Scheme.Hom.normalizationDesc_comp_assoc, IsIso.inv_hom_id_assoc]
  · rintro c ⟨hc₁, hc₂⟩
    have hl : c ≫ p = 𝟙 T ≫ b := by rw [hc₂, Category.id_comp]
    have key : j.fromNormalization ≫ pullback.lift c (𝟙 T) hl = d := by
      apply Scheme.Hom.normalization.hom_ext j _ _ (pullback.snd p b)
      · rw [Scheme.Hom.toNormalization_fromNormalization_assoc, hd,
          Scheme.Hom.toNormalization_normalizationDesc]
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hc₁]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
      · rw [Category.assoc, pullback.lift_snd, Category.comp_id]
      · rw [hd, Scheme.Hom.normalizationDesc_comp]
    calc c = pullback.lift c (𝟙 T) hl ≫ pullback.fst p b := (pullback.lift_fst _ _ _).symm
      _ = inv j.fromNormalization ≫ (j.fromNormalization ≫ pullback.lift c (𝟙 T) hl) ≫
            pullback.fst p b := by rw [Category.assoc, IsIso.inv_hom_id_assoc]
      _ = _ := by rw [key]

/- English proof (translation)
The claim follows from `ext_of_isDominant_of_isSeparated p h₂ j h₁`.
-/
theorem lift_unique_of_isDominant (j : U ⟶ T) [IsDominant j] [IsReduced T] (p : Z ⟶ Y)
    [IsSeparated p] {c c' : T ⟶ Z} (h₁ : j ≫ c = j ≫ c') (h₂ : c ≫ p = c' ≫ p) : c = c' := ext_of_isDominant_of_isSeparated p h₂ j h₁

/- English proof (translation)
Use `⟨?_⟩` and prove the remaining obligations. Establish `h1 : genericPoint U ∈ Set.range (U.fromSpecStalk (genericPoint U))`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `specializes_rfl`. Use `Dense.mono (Set.singleton_subset_iff.mpr h1) ?_` and prove the remaining obligations.

Rewrite using `[dense_iff_closure_eq]`. Conclude with `genericPoint_spec U`.
-/
theorem isDominant_fromSpecStalk_genericPoint (U : Scheme.{u}) [IsIntegral U] :
    IsDominant (U.fromSpecStalk (genericPoint U)) := by
  refine ⟨?_⟩
  have h1 : genericPoint U ∈ Set.range (U.fromSpecStalk (genericPoint U)) := by
    rw [Scheme.range_fromSpecStalk]; exact specializes_rfl
  refine Dense.mono (Set.singleton_subset_iff.mpr h1) ?_
  rw [dense_iff_closure_eq]
  exact genericPoint_spec U

/- English proof (translation)
Set `_ : Field (U.presheaf.stalk (genericPoint U))` to `inferInstanceAs (Field U.functionField)`. Establish `hsub : ∀ p q : Spec (U.presheaf.stalk (genericPoint U)), p = q`. Introduce `p q`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Rewrite using `[(Ideal.eq_bot_or_top p.asIdeal).resolve_right p.isPrime.ne_top, (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top]`.

Rewrite using `[hsub (genericPoint _) (IsLocalRing.closedPoint _)]`. Establish `e : (U.fromSpecStalk (genericPoint U)).stalkMap (IsLocalRing.closedPoint _) = Scheme.stalkClosedPointTo (U.fromSpecStalk (genericPoint U)) ≫ (stalkClosedPointIso _).inv`. Simplify using `[Scheme.stalkClosedPointTo]`. Rewrite using `[e, Scheme.stalkClosedPointTo_fromSpecStalk]`. Use `infer_instance`.
-/
theorem isIso_stalkMap_fromSpecStalk_genericPoint (U : Scheme.{u}) [IsIntegral U] :
    IsIso ((U.fromSpecStalk (genericPoint U)).stalkMap (genericPoint _)) := by
  let _ : Field (U.presheaf.stalk (genericPoint U)) := inferInstanceAs (Field U.functionField)
  have hsub : ∀ p q : Spec (U.presheaf.stalk (genericPoint U)), p = q := by
    intro p q
    apply PrimeSpectrum.ext
    rw [(Ideal.eq_bot_or_top p.asIdeal).resolve_right p.isPrime.ne_top,
      (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top]
  rw [hsub (genericPoint _) (IsLocalRing.closedPoint _)]
  have e : (U.fromSpecStalk (genericPoint U)).stalkMap (IsLocalRing.closedPoint _) =
      Scheme.stalkClosedPointTo (U.fromSpecStalk (genericPoint U)) ≫
        (stalkClosedPointIso _).inv := by
    simp [Scheme.stalkClosedPointTo]
  rw [e, Scheme.stalkClosedPointTo_fromSpecStalk]
  infer_instance

/- English proof (translation)
Establish `hT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t)` using `fun t => inferInstance`. Set `_ : Field (U.presheaf.stalk (genericPoint U))` to `inferInstanceAs (Field U.functionField)`. Establish `hsub : ∀ x y : Spec (U.presheaf.stalk (genericPoint U)), x = y`. Introduce `x y`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises.

Rewrite using `[(Ideal.eq_bot_or_top x.asIdeal).resolve_right x.isPrime.ne_top, (Ideal.eq_bot_or_top y.asIdeal).resolve_right y.isPrime.ne_top]`. Establish `: Subsingleton (Spec (U.presheaf.stalk (genericPoint U)))` using `⟨hsub⟩`. Use `set η := U.fromSpecStalk (genericPoint U) with hη`. Use `isDominant_fromSpecStalk_genericPoint U` as an intermediate fact. Use `isIso_stalkMap_fromSpecStalk_genericPoint U` as an intermediate fact.

Establish `hgen : η (genericPoint _) = genericPoint U` using `apply_genericPoint_of_isDominant η`. Establish `: IsIso ((η ≫ j).stalkMap (genericPoint _))`. Rewrite using `[Scheme.Hom.stalkMap_comp]`. Establish `hj : ∀ y (_ : y = genericPoint U), IsIso (j.stalkMap y)`. Introduce and unpack `_ rfl`.

Use `infer_instance`. Conclude with `IsIso.comp_isIso' (hj _ hgen) (isIso_stalkMap_fromSpecStalk_genericPoint U)`. Establish `: QuasiCompact (η ≫ j)` using `⟨fun _ _ _ => (Set.toFinite _).isCompact⟩`. Establish `: QuasiSeparated (η ≫ j)` using `⟨⟨fun _ _ _ => (Set.toFinite _).isCompact⟩⟩`. Use `isIso_fromNormalization_of_birational (η ≫ j) hT` as an intermediate fact.

Take `⟨c, ⟨hc₁, hc₂⟩, hcu⟩` from `existsUnique_lift_of_isIso_fromNormalization (η ≫ j) p (η ≫ a) b (by rw [Category.assoc, h, Category.assoc])`. Establish `hjc : j ≫ c = a` using `lift_unique_of_isDominant η p (by rw [← Category.assoc, hc₁]) (by rw [Category.assoc, hc₂, h])`. Conclude with `⟨c, ⟨hjc, hc₂⟩, fun c' hc' => hcu c' ⟨by rw [Category.assoc, hc'.1], hc'.2⟩⟩`.
-/
theorem existsUnique_lift_of_birational (j : U ⟶ T) [IsIntegral U] [IsIntegral T]
    [IsNormalScheme T] [IsDominant j] [IsIso (j.stalkMap (genericPoint U))]
    (p : Z ⟶ Y) [IsIntegralHom p] (a : U ⟶ Z) (b : T ⟶ Y) (h : a ≫ p = j ≫ b) :
    ∃! c : T ⟶ Z, j ≫ c = a ∧ c ≫ p = b := by
  have hT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) := fun t => inferInstance
  let _ : Field (U.presheaf.stalk (genericPoint U)) := inferInstanceAs (Field U.functionField)
  have hsub : ∀ x y : Spec (U.presheaf.stalk (genericPoint U)), x = y := by
    intro x y
    apply PrimeSpectrum.ext
    rw [(Ideal.eq_bot_or_top x.asIdeal).resolve_right x.isPrime.ne_top,
      (Ideal.eq_bot_or_top y.asIdeal).resolve_right y.isPrime.ne_top]
  have : Subsingleton (Spec (U.presheaf.stalk (genericPoint U))) := ⟨hsub⟩
  set η := U.fromSpecStalk (genericPoint U) with hη
  have := isDominant_fromSpecStalk_genericPoint U
  have := isIso_stalkMap_fromSpecStalk_genericPoint U
  have hgen : η (genericPoint _) = genericPoint U := apply_genericPoint_of_isDominant η
  have : IsIso ((η ≫ j).stalkMap (genericPoint _)) := by
    rw [Scheme.Hom.stalkMap_comp]
    have hj : ∀ y (_ : y = genericPoint U), IsIso (j.stalkMap y) := by
      rintro _ rfl; infer_instance
    exact IsIso.comp_isIso' (hj _ hgen) (isIso_stalkMap_fromSpecStalk_genericPoint U)
  have : QuasiCompact (η ≫ j) := ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩
  have : QuasiSeparated (η ≫ j) := ⟨⟨fun _ _ _ => (Set.toFinite _).isCompact⟩⟩
  have := isIso_fromNormalization_of_birational (η ≫ j) hT
  obtain ⟨c, ⟨hc₁, hc₂⟩, hcu⟩ :=
    existsUnique_lift_of_isIso_fromNormalization (η ≫ j) p (η ≫ a) b
      (by rw [Category.assoc, h, Category.assoc])
  have hjc : j ≫ c = a :=
    lift_unique_of_isDominant η p (by rw [← Category.assoc, hc₁]) (by rw [Category.assoc, hc₂, h])
  exact ⟨c, ⟨hjc, hc₂⟩, fun c' hc' => hcu c' ⟨by rw [Category.assoc, hc'.1], hc'.2⟩⟩

/- English proof (translation)
Establish `hloc : ∀ t : T, ∃ W : T.Opens, t ∈ W ∧ IsIrreducible (W : Set T)`. Introduce `t`. Establish `ht : t ∈ (⨆ V : T.affineOpens, (V : T.Opens))`. Rewrite using `[iSup_affineOpens_eq_top]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨V, htV⟩` from `TopologicalSpace.Opens.mem_iSup.mp ht`. Establish `: IsNoetherianRing Γ(T, V)` using `IsLocallyNoetherian.component_noetherian V`. Establish `: NoetherianSpace (V : T.Opens)` using `noetherianSpace_of_isAffineOpen V.1 V.2`. Use `set V' : T.Opens := V.1`. Set `x0 : V'` to `⟨t, htV⟩`.

Establish `hGT : IsIrreducible {y : T | y ⤳ t}`. Rewrite using `[← Scheme.range_fromSpecStalk, ← Set.image_univ]`. Conclude with `(IrreducibleSpace.isIrreducible_univ _).image _ (T.fromSpecStalk t).continuous.continuousOn`. Establish `hG : IsIrreducible {v : V' | v ⤳ x0}`. Use `⟨⟨x0, specializes_rfl⟩, ?_⟩` and prove the remaining obligations.

Establish `heq : {v : V' | v ⤳ x0} = Subtype.val ⁻¹' {y : T | y ⤳ t}`. Use extensionality with `v`. Conclude with `(Topology.IsInducing.subtypeVal.specializes_iff).symm`. Rewrite using `[heq]`. Conclude with `hGT.2.preimage V'.2.isOpenEmbedding_subtypeVal`.

Establish `huniq : ∀ Z ∈ irreducibleComponents V', x0 ∈ Z → Z = closure {v | v ⤳ x0}`. Introduce `Z hZ hx0`. Take `⟨ζ, hζ⟩` from `QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)`. Establish `hsub : Z ⊆ closure {v | v ⤳ x0}`. Rewrite using `[← (hζ : closure {ζ} = Z)]`.

Conclude with `closure_mono (Set.singleton_subset_iff.mpr (hζ.specializes hx0))`. Conclude with `le_antisymm hsub (hZ.2 hG.closure hsub)`. Establish `hS : irreducibleComponent x0 ∈ irreducibleComponents V'` using `irreducibleComponent_mem_irreducibleComponents x0`. Establish `hα` using `NoetherianSpace.finite_irreducibleComponents (α := V')`. Set `O` to `(⋃₀ (irreducibleComponents V' \ {irreducibleComponent x0}))ᶜ`.

Establish `hOo : IsOpen O` using `by show IsOpen (⋃₀ (irreducibleComponents V' \ {irreducibleComponent x0}))ᶜ`. Rewrite using `[Set.sUnion_eq_biUnion, isOpen_compl_iff]`. Conclude with `hα.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1`. Establish `hOS : O ⊆ irreducibleComponent x0` using `subset_closure.trans (closure_sUnion_irreducibleComponents_sdiff_singleton hα _ hS).le`. Establish `hx0O : x0 ∈ O`.

Introduce `hmem`. Take `⟨Z, ⟨hZ, hZS⟩, hx0Z⟩` from `hmem`. Conclude with `hZS ((huniq Z hZ hx0Z).trans (huniq _ hS mem_irreducibleComponent).symm)`. Establish `hOirr : IsIrreducible O` using `⟨⟨x0, hx0O⟩, isIrreducible_irreducibleComponent.2.open_subset hOo hOS⟩`. Conclude with `⟨⟨Subtype.val '' O, V'.2.isOpenMap_subtype_val O hOo⟩, ⟨x0, hx0O, rfl⟩, hOirr.image _ continuous_subtype_val.continuousOn⟩`.

It suffices to establish `IsIso j.fromNormalization from existsUnique_lift_of_isIso_fromNormalization j p a b h`. Apply `IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := MorphismProperty.isomorphisms Scheme)` to reduce the goal to its premises. Introduce `t`. Take `⟨W, htW, hW⟩` from `hloc t`. Use `⟨W, htW, ?_⟩` and prove the remaining obligations.

Establish `: IrreducibleSpace W` using `Subtype.irreducibleSpace hW`. Establish `: IsIntegral W.toScheme` using `isIntegral_of_irreducibleSpace_of_isReduced _`. Take `⟨u, hu⟩ : ∃ u : U, j u ∈ W` from `j.denseRange.exists_mem_open W.2 ⟨t, htW⟩`. Take `⟨z, -, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := j) (g := W.ι) u ⟨j u, hu⟩ rfl`. Establish `: Nonempty ↥(pullback j W.ι)` using `⟨z⟩`.

Establish `: IsIntegral (pullback j W.ι)` using `isIntegral_of_isOpenImmersion (pullback.snd j W.ι)`. Establish `: IsDominant (pullback.snd j W.ι)` using `⟨(pullback.snd j W.ι).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩`. Establish `hY : ∀ w : W.toScheme, IsIntegrallyClosed (W.toScheme.presheaf.stalk w)` using `fun w => inferInstance`. Use `isIso_fromNormalization_of_birational (pullback.snd j W.ι) hY` as an intermediate fact. Establish `e' : pullback.snd j.fromNormalization W.ι = inv (j.normalizationPullback W.ι) ≫ (pullback.snd j W.ι).fromNormalization` using `(IsIso.eq_inv_comp _).mpr (Scheme.Hom.normalizationPullback_snd j W.ι)`.

Establish `: IsIso (pullback.snd j.fromNormalization W.ι)` using `by rw [e']; infer_instance`. Use `show IsIso ((pullbackRestrictIsoRestrict _ _).inv ≫ pullback.snd _ _)`. Use `infer_instance`.
-/
theorem existsUnique_lift_of_isOpenImmersion_of_isDominant (j : U ⟶ T) [IsOpenImmersion j]
    [IsDominant j] [IsNormalScheme T] [IsLocallyNoetherian T]
    (p : Z ⟶ Y) [IsIntegralHom p] (a : U ⟶ Z) (b : T ⟶ Y) (h : a ≫ p = j ≫ b) :
    ∃! c : T ⟶ Z, j ≫ c = a ∧ c ≫ p = b := by
  have hloc : ∀ t : T, ∃ W : T.Opens, t ∈ W ∧ IsIrreducible (W : Set T) := by
    intro t
    have ht : t ∈ (⨆ V : T.affineOpens, (V : T.Opens)) := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨V, htV⟩ := TopologicalSpace.Opens.mem_iSup.mp ht
    have : IsNoetherianRing Γ(T, V) := IsLocallyNoetherian.component_noetherian V
    have : NoetherianSpace (V : T.Opens) := noetherianSpace_of_isAffineOpen V.1 V.2
    set V' : T.Opens := V.1
    let x0 : V' := ⟨t, htV⟩
    have hGT : IsIrreducible {y : T | y ⤳ t} := by
      rw [← Scheme.range_fromSpecStalk, ← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _
        (T.fromSpecStalk t).continuous.continuousOn
    have hG : IsIrreducible {v : V' | v ⤳ x0} := by
      refine ⟨⟨x0, specializes_rfl⟩, ?_⟩
      have heq : {v : V' | v ⤳ x0} = Subtype.val ⁻¹' {y : T | y ⤳ t} := by
        ext v; exact (Topology.IsInducing.subtypeVal.specializes_iff).symm
      rw [heq]
      exact hGT.2.preimage V'.2.isOpenEmbedding_subtypeVal
    have huniq : ∀ Z ∈ irreducibleComponents V', x0 ∈ Z → Z = closure {v | v ⤳ x0} := by
      intro Z hZ hx0
      obtain ⟨ζ, hζ⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
      have hsub : Z ⊆ closure {v | v ⤳ x0} := by
        rw [← (hζ : closure {ζ} = Z)]
        exact closure_mono (Set.singleton_subset_iff.mpr (hζ.specializes hx0))
      exact le_antisymm hsub (hZ.2 hG.closure hsub)
    have hS : irreducibleComponent x0 ∈ irreducibleComponents V' :=
      irreducibleComponent_mem_irreducibleComponents x0
    have hα := NoetherianSpace.finite_irreducibleComponents (α := V')
    let O := (⋃₀ (irreducibleComponents V' \ {irreducibleComponent x0}))ᶜ
    have hOo : IsOpen O := by
      show IsOpen (⋃₀ (irreducibleComponents V' \ {irreducibleComponent x0}))ᶜ
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact hα.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
    have hOS : O ⊆ irreducibleComponent x0 :=
      subset_closure.trans (closure_sUnion_irreducibleComponents_sdiff_singleton hα _ hS).le
    have hx0O : x0 ∈ O := by
      intro hmem
      obtain ⟨Z, ⟨hZ, hZS⟩, hx0Z⟩ := hmem
      exact hZS ((huniq Z hZ hx0Z).trans (huniq _ hS mem_irreducibleComponent).symm)
    have hOirr : IsIrreducible O :=
      ⟨⟨x0, hx0O⟩, isIrreducible_irreducibleComponent.2.open_subset hOo hOS⟩
    exact ⟨⟨Subtype.val '' O, V'.2.isOpenMap_subtype_val O hOo⟩, ⟨x0, hx0O, rfl⟩,
      hOirr.image _ continuous_subtype_val.continuousOn⟩
  suffices IsIso j.fromNormalization from existsUnique_lift_of_isIso_fromNormalization j p a b h
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro t
  obtain ⟨W, htW, hW⟩ := hloc t
  refine ⟨W, htW, ?_⟩
  have : IrreducibleSpace W := Subtype.irreducibleSpace hW
  have : IsIntegral W.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  obtain ⟨u, hu⟩ : ∃ u : U, j u ∈ W := j.denseRange.exists_mem_open W.2 ⟨t, htW⟩
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := j) (g := W.ι) u ⟨j u, hu⟩ rfl
  have : Nonempty ↥(pullback j W.ι) := ⟨z⟩
  have : IsIntegral (pullback j W.ι) := isIntegral_of_isOpenImmersion (pullback.snd j W.ι)
  have : IsDominant (pullback.snd j W.ι) :=
    ⟨(pullback.snd j W.ι).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have hY : ∀ w : W.toScheme, IsIntegrallyClosed (W.toScheme.presheaf.stalk w) :=
    fun w => inferInstance
  have := isIso_fromNormalization_of_birational (pullback.snd j W.ι) hY
  have e' : pullback.snd j.fromNormalization W.ι =
      inv (j.normalizationPullback W.ι) ≫ (pullback.snd j W.ι).fromNormalization :=
    (IsIso.eq_inv_comp _).mpr (Scheme.Hom.normalizationPullback_snd j W.ι)
  have : IsIso (pullback.snd j.fromNormalization W.ι) := by rw [e']; infer_instance
  show IsIso ((pullbackRestrictIsoRestrict _ _).inv ≫ pullback.snd _ _)
  infer_instance

end Abstract

section Affine

/- English proof (translation)
Use `set f := Spec.map (CommRingCat.ofHom (algebraMap R R')) with hf`. Establish `: IsAffine f.normalization` using `isAffine_of_isAffineHom f.fromNormalization`. Rewrite using `[← MorphismProperty.isomorphisms.iff, (MorphismProperty.isomorphisms _).arrow_mk_iso_iff (arrowIsoSpecΓOfIsAffine _), MorphismProperty.isomorphisms.iff]`. It suffices to establish `h : IsIso (f.fromNormalization.app ⊤) by`. Establish `: IsIso f.fromNormalization.appTop` using `h`.

Use `infer_instance`. Rewrite using `[f.fromNormalization_app (isAffineOpen_top (Spec (.of R)))]`. Set `_` to `(f.app ⊤).hom.toAlgebra`. Set `eR` to `Scheme.ΓSpecIso (.of R)`. Set `eR' : Γ(Spec (.of R'), f ⁻¹ᵁ ⊤) ≅ CommRingCat.of R'` to `Scheme.ΓSpecIso (.of R')`.

Establish `hnat : ∀ x, eR'.hom (algebraMap Γ(Spec (.of R), ⊤) Γ(Spec (.of R'), f ⁻¹ᵁ ⊤) x) = algebraMap R R' (eR.hom x)` using `fun x => congrArg (fun g => g.hom x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R R')))`. Establish `hinj : ∀ y, eR'.inv (eR'.hom y) = y` using `fun y => eR'.hom_inv_id_apply y`. Establish `hic : IsIntegrallyClosedIn Γ(Spec (.of R), ⊤) Γ(Spec (.of R'), f ⁻¹ᵁ ⊤)`. Rewrite using `[isIntegrallyClosedIn_iff]`. Use `⟨fun x y hxy => ?_, fun {x} hx => ?_⟩` and prove the remaining obligations.

Establish `h1` using `congrArg eR'.hom hxy`. Rewrite `h1` using `[hnat, hnat]`. Establish `h2` using `IsIntegralClosure.algebraMap_injective R R R' h1`. Simplify using `using congrArg eR.inv h2`. Establish `hx' : IsIntegral R (eR'.hom.hom x)` using `IsIntegral.map_of_comp_eq eR.hom.hom eR'.hom.hom (RingHom.ext fun z => (hnat z).symm) hx`.

Take `⟨y, hy⟩` from `(IsIntegralClosure.isIntegral_iff (A := R)).mp hx'`. Use `⟨eR.inv y, ?_⟩` and prove the remaining obligations. Rewrite using `[← hinj (algebraMap _ _ (eR.inv y)), ← hinj x, hnat, Iso.inv_hom_id_apply]`. Conclude with `congrArg (fun z => eR'.inv z) hy`. Establish `hbij : Function.Bijective (algebraMap Γ(Spec (.of R), ⊤) (integralClosure Γ(Spec (.of R), ⊤) Γ(Spec (.of R'), f ⁻¹ᵁ ⊤)))`.

Use `⟨fun x y hxy => IsIntegralClosure.algebraMap_injective _ Γ(Spec (.of R), ⊤) _ (congrArg Subtype.val hxy), ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨z, hz⟩`. Take `⟨y, rfl⟩` from `(IsIntegralClosure.isIntegral_iff (A := Γ(Spec (.of R), ⊤))).mp hz`. Conclude with `⟨y, rfl⟩`. Establish `: IsIso (CommRingCat.ofHom (algebraMap Γ(Spec (.of R), ⊤) (integralClosure Γ(Spec (.of R), ⊤) Γ(Spec (.of R'), f ⁻¹ᵁ ⊤))))` using `(ConcreteCategory.isIso_iff_bijective _).mpr hbij`.

Use `infer_instance`.
-/
theorem isIso_fromNormalization_spec_of_isIntegrallyClosedIn (R R' : Type u) [CommRing R]
    [CommRing R'] [Algebra R R'] [IsIntegrallyClosedIn R R'] :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap R R'))).fromNormalization := by
  set f := Spec.map (CommRingCat.ofHom (algebraMap R R')) with hf
  have : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  rw [← MorphismProperty.isomorphisms.iff, (MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (arrowIsoSpecΓOfIsAffine _), MorphismProperty.isomorphisms.iff]
  suffices h : IsIso (f.fromNormalization.app ⊤) by
    have : IsIso f.fromNormalization.appTop := h
    infer_instance
  rw [f.fromNormalization_app (isAffineOpen_top (Spec (.of R)))]
  let _ := (f.app ⊤).hom.toAlgebra
  let eR := Scheme.ΓSpecIso (.of R)
  let eR' : Γ(Spec (.of R'), f ⁻¹ᵁ ⊤) ≅ CommRingCat.of R' := Scheme.ΓSpecIso (.of R')
  have hnat : ∀ x, eR'.hom (algebraMap Γ(Spec (.of R), ⊤) Γ(Spec (.of R'), f ⁻¹ᵁ ⊤) x) =
      algebraMap R R' (eR.hom x) := fun x =>
    congrArg (fun g => g.hom x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R R')))
  have hinj : ∀ y, eR'.inv (eR'.hom y) = y := fun y => eR'.hom_inv_id_apply y
  have hic : IsIntegrallyClosedIn Γ(Spec (.of R), ⊤) Γ(Spec (.of R'), f ⁻¹ᵁ ⊤) := by
    rw [isIntegrallyClosedIn_iff]
    refine ⟨fun x y hxy => ?_, fun {x} hx => ?_⟩
    · have h1 := congrArg eR'.hom hxy
      rw [hnat, hnat] at h1
      have h2 := IsIntegralClosure.algebraMap_injective R R R' h1
      simpa using congrArg eR.inv h2
    · have hx' : IsIntegral R (eR'.hom.hom x) :=
        IsIntegral.map_of_comp_eq eR.hom.hom eR'.hom.hom
          (RingHom.ext fun z => (hnat z).symm) hx
      obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := R)).mp hx'
      refine ⟨eR.inv y, ?_⟩
      rw [← hinj (algebraMap _ _ (eR.inv y)), ← hinj x, hnat, Iso.inv_hom_id_apply]
      exact congrArg (fun z => eR'.inv z) hy
  have hbij : Function.Bijective (algebraMap Γ(Spec (.of R), ⊤)
      (integralClosure Γ(Spec (.of R), ⊤) Γ(Spec (.of R'), f ⁻¹ᵁ ⊤))) := by
    refine ⟨fun x y hxy => IsIntegralClosure.algebraMap_injective _ Γ(Spec (.of R), ⊤) _
      (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := (IsIntegralClosure.isIntegral_iff (A := Γ(Spec (.of R), ⊤))).mp hz
    exact ⟨y, rfl⟩
  have : IsIso (CommRingCat.ofHom (algebraMap Γ(Spec (.of R), ⊤)
      (integralClosure Γ(Spec (.of R), ⊤) Γ(Spec (.of R'), f ⁻¹ᵁ ⊤)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  infer_instance

/- English proof (translation)
Establish `hKR : IsIntegrallyClosedIn R K` using `(isIntegrallyClosed_iff_isIntegrallyClosedIn K).mp ‹_›`. Conclude with `(IsScalarTower.toAlgHom R R' K).isIntegrallyClosedIn hK hKR`.
-/
theorem isIntegrallyClosedIn_of_injective_fractionRing (R R' K : Type*) [CommRing R] [CommRing R']
    [CommRing K] [Algebra R R'] [Algebra R K] [Algebra R' K] [IsScalarTower R R' K]
    [IsFractionRing R K] [IsIntegrallyClosed R] (hK : Function.Injective (algebraMap R' K)) :
    IsIntegrallyClosedIn R R' := by
  have hKR : IsIntegrallyClosedIn R K := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mp ‹_›
  exact (IsScalarTower.toAlgHom R R' K).isIntegrallyClosedIn hK hKR

/- English proof (translation)
Set `K` to `FractionRing R`. Set `_ : Algebra R' K` to `IsLocalization.localizationAlgebraOfSubmonoidLe R' K M (nonZeroDivisors R) hM`. Establish `: IsScalarTower R R' K` using `IsLocalization.localization_isScalarTower_of_submonoid_le R' K M (nonZeroDivisors R) hM`. Use `isIntegrallyClosedIn_of_injective_fractionRing R R' K ?_` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Take `⟨⟨r, m⟩, rfl⟩` from `IsLocalization.mk'_surjective M x`. Establish `h0 : algebraMap R K r = 0`. Establish `h2` using `congrArg (algebraMap R' K) (IsLocalization.mk'_spec R' r m)`. Rewrite `h2` using `[map_mul, hx, zero_mul, ← IsScalarTower.algebraMap_apply]`.

Conclude with `h2.symm`. Establish `hr : r = 0` using `IsFractionRing.injective R K (by rw [h0, map_zero])`. Simplify using `[hr]`.
-/
theorem isIntegrallyClosedIn_of_isLocalization {R : Type*} [CommRing R] [IsIntegrallyClosed R]
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R) (R' : Type*) [CommRing R'] [Algebra R R']
    [IsLocalization M R'] : IsIntegrallyClosedIn R R' := by
  let K := FractionRing R
  let _ : Algebra R' K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe R' K M (nonZeroDivisors R) hM
  have : IsScalarTower R R' K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le R' K M (nonZeroDivisors R) hM
  refine isIntegrallyClosedIn_of_injective_fractionRing R R' K ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
  have h0 : algebraMap R K r = 0 := by
    have h2 := congrArg (algebraMap R' K) (IsLocalization.mk'_spec R' r m)
    rw [map_mul, hx, zero_mul, ← IsScalarTower.algebraMap_apply] at h2
    exact h2.symm
  have hr : r = 0 := IsFractionRing.injective R K (by rw [h0, map_zero])
  simp [hr]

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {Z Y : Scheme.{u}}

/- English proof (translation)
Use `isIso_fromNormalization_spec_of_isIntegrallyClosedIn R R'` as an intermediate fact. Conclude with `existsUnique_lift_of_isIso_fromNormalization _ p a b h`.
-/
theorem existsUnique_lift_spec_of_isIntegrallyClosedIn [IsIntegrallyClosedIn R R']
    (p : Z ⟶ Y) [IsIntegralHom p] (a : Spec (.of R') ⟶ Z) (b : Spec (.of R) ⟶ Y)
    (h : a ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ b) :
    ∃! c : Spec (.of R) ⟶ Z,
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ c = a ∧ c ≫ p = b := by
  have := isIso_fromNormalization_spec_of_isIntegrallyClosedIn R R'
  exact existsUnique_lift_of_isIso_fromNormalization _ p a b h

/- English proof (translation)
Use `isIntegrallyClosedIn_of_isLocalization M hM R'` as an intermediate fact. Conclude with `existsUnique_lift_spec_of_isIntegrallyClosedIn p a b h`.
-/
theorem existsUnique_lift_spec_of_isLocalization [IsIntegrallyClosed R] (M : Submonoid R)
    (hM : M ≤ nonZeroDivisors R) [IsLocalization M R']
    (p : Z ⟶ Y) [IsIntegralHom p] (a : Spec (.of R') ⟶ Z) (b : Spec (.of R) ⟶ Y)
    (h : a ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ b) :
    ∃! c : Spec (.of R) ⟶ Z,
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ c = a ∧ c ≫ p = b := by
  have := isIntegrallyClosedIn_of_isLocalization M hM R'
  exact existsUnique_lift_spec_of_isIntegrallyClosedIn p a b h

end Affine

section Normalization

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/- English proof (translation)
The claim follows from `existsUnique_lift_spec_of_isLocalization M hM f.fromNormalization (χ₁ ≫ f.toNormalization) χ₀ (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, h])`.
-/
theorem existsUnique_lift_normalization_spec_of_isLocalization [IsIntegrallyClosed R]
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R) [IsLocalization M R']
    (χ₀ : Spec (.of R) ⟶ Y) (χ₁ : Spec (.of R') ⟶ X)
    (h : χ₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ χ₀) :
    ∃! χ : Spec (.of R) ⟶ f.normalization,
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ χ = χ₁ ≫ f.toNormalization ∧
        χ ≫ f.fromNormalization = χ₀ :=
  existsUnique_lift_spec_of_isLocalization M hM f.fromNormalization (χ₁ ≫ f.toNormalization) χ₀
    (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, h])

end Normalization

section Sections

variable {U T Z : Scheme.{u}}

end Sections

end GlobalTheory
