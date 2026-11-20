import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

noncomputable section

variable {k : Type u} [Field k] {X W : Scheme.{u}}

/- English proof (authored)
Associate the first composite so that the original map of schemes is followed by the original structural map. The resulting equality is commutativity of the base-change square for the composite structural map.
-/
private theorem pullbackCondition_baseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
    (K : Type u) [Field K] [Algebra k K] :
    (baseChangeProjection (c ≫ f) K ≫ c) ≫ f = baseChangeToSpec (c ≫ f) K ≫ specMapAlgebraMap k K := by
  rw [Category.assoc]
  exact pullback.condition

def baseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
    (K : Type u) [Field K] [Algebra k K] :
    baseChange (c ≫ f) K ⟶ baseChange f K :=
  pullback.lift (baseChangeProjection (c ≫ f) K ≫ c) (baseChangeToSpec (c ≫ f) K)
    (pullbackCondition_baseChangeMap f c K)

@[simp]
/- English proof (authored)
The first component of the induced map into the base change is the projection to the original source followed by the given map. The first projection of the pullback recovers this component.
-/
theorem baseChangeMap_comp_baseChangeProjection (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
    (K : Type u) [Field K] [Algebra k K] :
    baseChangeMap f c K ≫ baseChangeProjection f K = baseChangeProjection (c ≫ f) K ≫ c :=
  pullback.lift_fst _ _ _

@[simp]
/- English proof (authored)
The second component of the induced map is the source structural map to the extension field. Composing the induced map with the target's second projection recovers that component.
-/
theorem baseChangeMap_comp_baseChangeToSpec (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
    (K : Type u) [Field K] [Algebra k K] :
    baseChangeMap f c K ≫ baseChangeToSpec f K = baseChangeToSpec (c ≫ f) K :=
  pullback.lift_snd _ _ _

/- English proof (authored)
The square identifies its top map with the base change of its bottom map along the other side. Stability under base change transfers the property of the bottom map to the top map.
-/
private theorem morphismProperty_of_isPullback {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {A B C' D : Scheme.{u}} {h : A ⟶ B} {v : A ⟶ C'} {v' : B ⟶ D}
    {b : C' ⟶ D} (sq : IsPullback h v v' b) (hb : P b) : P h :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip hb

/- English proof (authored)
Place the proposed comparison square beside the base-change square for the target. The right square is a pullback, and the outer rectangle is the base-change square for the source because the induced map respects the structural maps to the extension field. The comparison square commutes by the formula for the first projection. Pullback cancellation gives the claim.
-/
private theorem isPullback_baseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
    (K : Type u) [Field K] [Algebra k K] :
    IsPullback (baseChangeMap f c K) (baseChangeProjection (c ≫ f) K) (baseChangeProjection f K) c := by
  have h1 : IsPullback (baseChangeToSpec (c ≫ f) K) (baseChangeProjection (c ≫ f) K)
      (specMapAlgebraMap k K) (c ≫ f) := (IsPullback.of_hasPullback (c ≫ f) (specMapAlgebraMap k K)).flip
  have h2 : IsPullback (baseChangeToSpec f K) (baseChangeProjection f K) (specMapAlgebraMap k K) f :=
    (IsPullback.of_hasPullback f (specMapAlgebraMap k K)).flip
  refine IsPullback.of_right ?_ (baseChangeMap_comp_baseChangeProjection f c K) h2
  rw [baseChangeMap_comp_baseChangeToSpec]
  exact h1

/- English proof (authored)
The comparison square identifies the induced map with the pullback of the given étale map. Étaleness is preserved under this base change.
-/
theorem etale_baseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [Etale c]
    (K : Type u) [Field K] [Algebra k K] : Etale (baseChangeMap f c K) :=
  morphismProperty_of_isPullback (P := @Etale) (isPullback_baseChangeMap f c K) ‹Etale c›

instance instEtaleBaseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [Etale c]
    (K : Type u) [Field K] [Algebra k K] : Etale (baseChangeMap f c K) :=
  etale_baseChangeMap f c K

/- English proof (authored)
The comparison square identifies the induced map with the pullback of the given surjection. Surjectivity of scheme morphisms is preserved under base change.
-/
theorem surjective_baseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [Surjective c]
    (K : Type u) [Field K] [Algebra k K] : Surjective (baseChangeMap f c K) :=
  morphismProperty_of_isPullback (P := @Surjective) (isPullback_baseChangeMap f c K) ‹Surjective c›

instance instSurjectiveBaseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [Surjective c]
    (K : Type u) [Field K] [Algebra k K] : Surjective (baseChangeMap f c K) :=
  surjective_baseChangeMap f c K

/- English proof (authored)
The map between the spectra of the fields is affine. Its pullback is the projection from the extended scheme to the original one, hence this projection is affine. Since its target is affine, its source is affine.
-/
theorem isAffine_baseChange (p : W ⟶ Spec (CommRingCat.of k)) [IsAffine W]
    (K : Type u) [Field K] [Algebra k K] : IsAffine (baseChange p K) := by
  have : IsAffineHom (baseChangeProjection p K) :=
    morphismProperty_of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback p (specMapAlgebraMap k K))
      inferInstance
  exact isAffine_of_isAffineHom (f := baseChangeProjection p K)

/- English proof (authored)
The composite is a structural map from the given affine source to the field spectrum. Apply affineness of field base change to this structural map.
-/
theorem isAffine_baseChange_comp (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [IsAffine W]
    (K : Type u) [Field K] [Algebra k K] : IsAffine (baseChange (c ≫ f) K) :=
  isAffine_baseChange (c ≫ f) K

/- English proof (authored)
A scheme is reduced exactly when its local rings are reduced. The hypothesis supplies this condition at every point.
-/
private theorem isReduced_of_isReduced_stalk (Y : Scheme.{u})
    (h : ∀ y : ↥Y, _root_.IsReduced (Y.presheaf.stalk y)) : IsReduced Y := by
  have : ∀ y : ↥Y, _root_.IsReduced (Y.presheaf.stalk y) := h
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk Y

/- English proof (authored)
The map on local rings at a point of an open subscheme is an isomorphism. The local ring on the open subscheme embeds into the reduced local ring on the target via the inverse map, so it is reduced.
-/
private theorem isReduced_stalk_of_isOpenImmersion {A B : Scheme.{u}} (w : A ⟶ B)
    [IsOpenImmersion w] [IsReduced B] (a : ↥A) : _root_.IsReduced (A.presheaf.stalk a) :=
  isReduced_of_injective (CategoryTheory.inv (w.stalkMap a)).hom
    (ConcreteCategory.bijective_of_isIso (CategoryTheory.inv (w.stalkMap a))).1

/- English proof (authored)
Choose a point over any given point of the target using the covering condition. Its open immersion identifies the two local rings. The source local ring is reduced by hypothesis, so the target local ring is reduced. This holds at every point.
-/
private theorem isReduced_of_isReduced_stalk_of_cover {Y : Scheme.{u}} {ι : Type u} {Z : ι → Scheme.{u}}
    (j : ∀ i, Z i ⟶ Y) (hj : ∀ i, IsOpenImmersion (j i))
    (hZ : ∀ (i : ι) (z : ↥(Z i)), _root_.IsReduced ((Z i).presheaf.stalk z))
    (hcov : ∀ y : ↥Y, ∃ (i : ι) (z : ↥(Z i)), (j i).base z = y) : IsReduced Y := by
  refine isReduced_of_isReduced_stalk Y ?_
  intro y
  obtain ⟨i, z, rfl⟩ := hcov y
  have := hj i
  have := hZ i z
  exact isReduced_of_injective ((j i).stalkMap z).hom
    (ConcreteCategory.bijective_of_isIso ((j i).stalkMap z)).1

/- English proof (authored)
The inclusions of the summands form the canonical open cover of the disjoint union. Every point lies in the image of one of these inclusions, which supplies the index and the point.
-/
private theorem sigma_jointly_surjective {ι : Type u} (Z : ι → Scheme.{u}) (x : ↥(∐ Z)) :
    ∃ (i : ι) (y : ↥(Z i)), (Sigma.ι Z i).base y = x := by
  obtain ⟨y, hy⟩ := (sigmaOpenCover Z).covers x
  exact ⟨_, y, hy⟩

/- English proof (authored)
The two points lie over the same base point, so they admit a common lift to the scheme-theoretic fiber product. The second projection of this lift is the given point of the second scheme.
-/
private theorem exists_pullback_snd_base_eq {A B C' : Scheme.{u}} (g1 : A ⟶ C') (g2 : B ⟶ C')
    (a : ↥A) (b : ↥B) (h : g1.base a = g2.base b) :
    ∃ z : ↥(pullback g1 g2), (pullback.snd g1 g2).base z = b := by
  obtain ⟨z, _, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := g1) (g := g2) a b h
  exact ⟨z, hz2⟩

/- English proof (authored)
Pull back each summand inclusion along the projection from the extended disjoint union. These open immersions cover that union because every point projects to a point in one summand, and the two points have a common lift to the pullback. Each pulled-back summand also maps by an open immersion into the extended base scheme. This follows by pasting the two pullback squares and using that the original summand maps to the original base by its open inclusion. Since the extended base scheme is reduced, each covering summand has reduced stalks. The covering criterion gives reducedness of the extended disjoint union.
-/
theorem isReduced_baseChange_sigmaOpensDesc (f : X ⟶ Spec (CommRingCat.of k))
    (K : Type u) [Field K] [Algebra k K] [IsReduced (baseChange f K)]
    {ι : Type u} (U : ι → X.Opens) :
    IsReduced (baseChange (sigmaOpensDesc X U ≫ f) K) := by
  have hsq : ∀ i : ι, IsPullback
      (pullback.snd (Sigma.ι (fun i => (U i).toScheme) i)
          (baseChangeProjection (sigmaOpensDesc X U ≫ f) K) ≫
        baseChangeMap f (sigmaOpensDesc X U) K)
      (pullback.fst (Sigma.ι (fun i => (U i).toScheme) i)
        (baseChangeProjection (sigmaOpensDesc X U ≫ f) K))
      (baseChangeProjection f K) ((U i).ι) := by
    intro i
    have h := IsPullback.paste_horiz
      (IsPullback.of_hasPullback (Sigma.ι (fun i => (U i).toScheme) i)
        (baseChangeProjection (sigmaOpensDesc X U ≫ f) K)).flip
      (isPullback_baseChangeMap f (sigmaOpensDesc X U) K)
    rwa [sigma_ι_sigmaOpensDesc X U i] at h
  refine isReduced_of_isReduced_stalk_of_cover
    (Z := fun i => pullback (Sigma.ι (fun i => (U i).toScheme) i)
      (baseChangeProjection (sigmaOpensDesc X U ≫ f) K))
    (fun i => pullback.snd (Sigma.ι (fun i => (U i).toScheme) i)
      (baseChangeProjection (sigmaOpensDesc X U ≫ f) K))
    (fun i => inferInstance) (fun i z => ?_) ?_
  · have : IsOpenImmersion (pullback.snd (Sigma.ι (fun i => (U i).toScheme) i)
        (baseChangeProjection (sigmaOpensDesc X U ≫ f) K) ≫
        baseChangeMap f (sigmaOpensDesc X U) K) :=
      morphismProperty_of_isPullback (P := @IsOpenImmersion) (hsq i) inferInstance
    exact isReduced_stalk_of_isOpenImmersion
      (pullback.snd (Sigma.ι (fun i => (U i).toScheme) i)
        (baseChangeProjection (sigmaOpensDesc X U ≫ f) K) ≫
        baseChangeMap f (sigmaOpensDesc X U) K) z
  · intro p
    obtain ⟨i, y, hy⟩ := sigma_jointly_surjective (fun i => (U i).toScheme)
      ((baseChangeProjection (sigmaOpensDesc X U ≫ f) K).base p)
    obtain ⟨z, hz⟩ := exists_pullback_snd_base_eq (Sigma.ι (fun i => (U i).toScheme) i)
      (baseChangeProjection (sigmaOpensDesc X U ≫ f) K) y p hy
    exact ⟨i, z, hz⟩

/- English proof (authored)
Quasi-compactness over the field gives a finite affine open cover. Take the disjoint union of its members and the map given by the open inclusions. This union is affine and reduced, and the cover map is étale and surjective. Its structural map is locally of finite type and quasi-compact. After extending the field, affineness and both finiteness properties persist, while the reducedness criterion for the extended union applies because the extended base is reduced. The induced cover map is again étale and surjective by base change. Its two projection identities give the stated compatibilities.
-/
theorem exists_etale_surjective_affine_cover_baseChange (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X]
    (K : Type u) [Field K] [Algebra k K] [IsReduced (baseChange f K)] :
    ∃ (W : Scheme.{u}) (c : W ⟶ X) (g : baseChange (c ≫ f) K ⟶ baseChange f K),
      IsAffine W ∧ IsReduced W ∧ LocallyOfFiniteType (c ≫ f) ∧ QuasiCompact (c ≫ f) ∧
        Etale c ∧ Surjective c ∧
        IsAffine (baseChange (c ≫ f) K) ∧ IsReduced (baseChange (c ≫ f) K) ∧
        LocallyOfFiniteType (baseChangeToSpec (c ≫ f) K) ∧
        QuasiCompact (baseChangeToSpec (c ≫ f) K) ∧
        Etale g ∧ Surjective g ∧
        g ≫ baseChangeToSpec f K = baseChangeToSpec (c ≫ f) K ∧
        g ≫ baseChangeProjection f K = baseChangeProjection (c ≫ f) K ≫ c := by
  have : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace (f := f)
  obtain ⟨ι, hι, U, hUaff, hUtop⟩ := exists_finite_affine_cover X
  have := hι
  have hWaff : IsAffine (sigmaOpens X U) := isAffine_sigmaOpens X U hUaff
  have hsurj : Surjective (sigmaOpensDesc X U) := surjective_sigmaOpensDesc X U hUtop
  have hqc : QuasiCompact (sigmaOpensDesc X U ≫ f) := inferInstance
  have hbcaff : IsAffine (baseChange (sigmaOpensDesc X U ≫ f) K) :=
    isAffine_baseChange_comp f (sigmaOpensDesc X U) K
  refine ⟨sigmaOpens X U, sigmaOpensDesc X U, baseChangeMap f (sigmaOpensDesc X U) K,
    hWaff, inferInstance, inferInstance, hqc, inferInstance, hsurj, hbcaff,
    isReduced_baseChange_sigmaOpensDesc f K U, ?_, ?_, inferInstance, inferInstance,
    baseChangeMap_comp_baseChangeToSpec f (sigmaOpensDesc X U) K,
    baseChangeMap_comp_baseChangeProjection f (sigmaOpensDesc X U) K⟩
  · exact morphismProperty_of_isPullback (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback (sigmaOpensDesc X U ≫ f) (specMapAlgebraMap k K)).flip inferInstance
  · exact morphismProperty_of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback (sigmaOpensDesc X U ≫ f) (specMapAlgebraMap k K)).flip inferInstance

end

end FunctorialResolution.EmbeddedResolution
