import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

noncomputable section

variable {k : Type u} [Field k] {X W : Scheme.{u}}

/- English proof (translation)
Rewrite using `[Category.assoc]`. Conclude with `pullback.condition`.
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
/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _ @[simp]`.
-/
theorem baseChangeMap_comp_baseChangeProjection (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
    (K : Type u) [Field K] [Algebra k K] :
    baseChangeMap f c K ≫ baseChangeProjection f K = baseChangeProjection (c ≫ f) K ≫ c :=
  pullback.lift_fst _ _ _

@[simp]
/- English proof (translation)
The claim follows from `pullback.lift_snd _ _ _`.
-/
theorem baseChangeMap_comp_baseChangeToSpec (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X)
    (K : Type u) [Field K] [Algebra k K] :
    baseChangeMap f c K ≫ baseChangeToSpec f K = baseChangeToSpec (c ≫ f) K :=
  pullback.lift_snd _ _ _

/- English proof (translation)
The claim follows from `MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip hb`.
-/
private theorem morphismProperty_of_isPullback {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {A B C' D : Scheme.{u}} {h : A ⟶ B} {v : A ⟶ C'} {v' : B ⟶ D}
    {b : C' ⟶ D} (sq : IsPullback h v v' b) (hb : P b) : P h :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip hb

/- English proof (translation)
Establish `h1 : IsPullback (baseChangeToSpec (c ≫ f) K) (baseChangeProjection (c ≫ f) K) (specMapAlgebraMap k K) (c ≫ f)` using `(IsPullback.of_hasPullback (c ≫ f) (specMapAlgebraMap k K)).flip`. Establish `h2 : IsPullback (baseChangeToSpec f K) (baseChangeProjection f K) (specMapAlgebraMap k K) f` using `(IsPullback.of_hasPullback f (specMapAlgebraMap k K)).flip`. Use `IsPullback.of_right ?_ (baseChangeMap_comp_baseChangeProjection f c K) h2` and prove the remaining obligations. Rewrite using `[baseChangeMap_comp_baseChangeToSpec]`. Conclude with `h1`.
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

/- English proof (translation)
The claim follows from `morphismProperty_of_isPullback (P := @Etale) (isPullback_baseChangeMap f c K) ‹Etale c›`.
-/
theorem etale_baseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [Etale c]
    (K : Type u) [Field K] [Algebra k K] : Etale (baseChangeMap f c K) :=
  morphismProperty_of_isPullback (P := @Etale) (isPullback_baseChangeMap f c K) ‹Etale c›

instance instEtaleBaseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [Etale c]
    (K : Type u) [Field K] [Algebra k K] : Etale (baseChangeMap f c K) :=
  etale_baseChangeMap f c K

/- English proof (translation)
The claim follows from `morphismProperty_of_isPullback (P := @Surjective) (isPullback_baseChangeMap f c K) ‹Surjective c›`.
-/
theorem surjective_baseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [Surjective c]
    (K : Type u) [Field K] [Algebra k K] : Surjective (baseChangeMap f c K) :=
  morphismProperty_of_isPullback (P := @Surjective) (isPullback_baseChangeMap f c K) ‹Surjective c›

instance instSurjectiveBaseChangeMap (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [Surjective c]
    (K : Type u) [Field K] [Algebra k K] : Surjective (baseChangeMap f c K) :=
  surjective_baseChangeMap f c K

/- English proof (translation)
Establish `: IsAffineHom (baseChangeProjection p K)` using `morphismProperty_of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback p (specMapAlgebraMap k K)) inferInstance`. Conclude with `isAffine_of_isAffineHom (f := baseChangeProjection p K)`.
-/
theorem isAffine_baseChange (p : W ⟶ Spec (CommRingCat.of k)) [IsAffine W]
    (K : Type u) [Field K] [Algebra k K] : IsAffine (baseChange p K) := by
  have : IsAffineHom (baseChangeProjection p K) :=
    morphismProperty_of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback p (specMapAlgebraMap k K))
      inferInstance
  exact isAffine_of_isAffineHom (f := baseChangeProjection p K)

/- English proof (translation)
The claim follows from `isAffine_baseChange (c ≫ f) K`.
-/
theorem isAffine_baseChange_comp (f : X ⟶ Spec (CommRingCat.of k)) (c : W ⟶ X) [IsAffine W]
    (K : Type u) [Field K] [Algebra k K] : IsAffine (baseChange (c ≫ f) K) :=
  isAffine_baseChange (c ≫ f) K

/- English proof (translation)
Establish `: ∀ y : ↥Y, _root_.IsReduced (Y.presheaf.stalk y)` using `h`. Conclude with `AlgebraicGeometry.isReduced_of_isReduced_stalk Y`.
-/
private theorem isReduced_of_isReduced_stalk (Y : Scheme.{u})
    (h : ∀ y : ↥Y, _root_.IsReduced (Y.presheaf.stalk y)) : IsReduced Y := by
  have : ∀ y : ↥Y, _root_.IsReduced (Y.presheaf.stalk y) := h
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk Y

/- English proof (translation)
The claim follows from `isReduced_of_injective (CategoryTheory.inv (w.stalkMap a)).hom (ConcreteCategory.bijective_of_isIso (CategoryTheory.inv (w.stalkMap a))).1`.
-/
private theorem isReduced_stalk_of_isOpenImmersion {A B : Scheme.{u}} (w : A ⟶ B)
    [IsOpenImmersion w] [IsReduced B] (a : ↥A) : _root_.IsReduced (A.presheaf.stalk a) :=
  isReduced_of_injective (CategoryTheory.inv (w.stalkMap a)).hom
    (ConcreteCategory.bijective_of_isIso (CategoryTheory.inv (w.stalkMap a))).1

/- English proof (translation)
Use `isReduced_of_isReduced_stalk Y ?_` and prove the remaining obligations. Introduce `y`. Take `⟨i, z, rfl⟩` from `hcov y`. Use `hj i` as an intermediate fact. Use `hZ i z` as an intermediate fact.

Conclude with `isReduced_of_injective ((j i).stalkMap z).hom (ConcreteCategory.bijective_of_isIso ((j i).stalkMap z)).1`.
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

/- English proof (translation)
Take `⟨y, hy⟩` from `(sigmaOpenCover Z).covers x`. Conclude with `⟨_, y, hy⟩`.
-/
private theorem sigma_jointly_surjective {ι : Type u} (Z : ι → Scheme.{u}) (x : ↥(∐ Z)) :
    ∃ (i : ι) (y : ↥(Z i)), (Sigma.ι Z i).base y = x := by
  obtain ⟨y, hy⟩ := (sigmaOpenCover Z).covers x
  exact ⟨_, y, hy⟩

/- English proof (translation)
Take `⟨z, _, hz2⟩` from `Scheme.Pullback.exists_preimage_pullback (f := g1) (g := g2) a b h`. Conclude with `⟨z, hz2⟩`.
-/
private theorem exists_pullback_snd_base_eq {A B C' : Scheme.{u}} (g1 : A ⟶ C') (g2 : B ⟶ C')
    (a : ↥A) (b : ↥B) (h : g1.base a = g2.base b) :
    ∃ z : ↥(pullback g1 g2), (pullback.snd g1 g2).base z = b := by
  obtain ⟨z, _, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := g1) (g := g2) a b h
  exact ⟨z, hz2⟩

/- English proof (translation)
Establish `hsq : ∀ i : ι, IsPullback (pullback.snd (Sigma.ι (fun i => (U i).toScheme) i) (baseChangeProjection (sigmaOpensDesc X U ≫ f) K) ≫ baseChangeMap f (sigmaOpensDesc X U) K) (pullback.fst (Sigma.ι (fun i => (U i).toScheme) i) (baseChangeProjection (sigmaOpensDesc X U ≫ f) K)) (baseCh …`. Introduce `i`. Establish `h` using `IsPullback.paste_horiz (IsPullback.of_hasPullback (Sigma.ι (fun i => (U i).toScheme) i) (baseChangeProjection (sigmaOpensDesc X U ≫ f) K)).flip (isPullback_baseChangeMap f (sigmaOpensDesc X U) K)`. Rewrite `h` using `[sigma_ι_sigmaOpensDesc X U i]`. Then use the resulting hypothesis. Use `isReduced_of_isReduced_stalk_of_cover (Z := fun i => pullback (Sigma.ι (fun i => (U i).toScheme) i) (baseChangeProjection (sigmaOpensDesc X U ≫ f) K)) (fun i => pullback.snd (Sigma.ι (fun i => (U i).toScheme) i) (baseChangeProjection (sigmaOpensDesc X U ≫ f) K)) (fun i => inferIn …` and prove the remaining obligations.

Establish `: IsOpenImmersion (pullback.snd (Sigma.ι (fun i => (U i).toScheme) i) (baseChangeProjection (sigmaOpensDesc X U ≫ f) K) ≫ baseChangeMap f (sigmaOpensDesc X U) K)` using `morphismProperty_of_isPullback (P := @IsOpenImmersion) (hsq i) inferInstance`. Conclude with `isReduced_stalk_of_isOpenImmersion (pullback.snd (Sigma.ι (fun i => (U i).toScheme) i) (baseChangeProjection (sigmaOpensDesc X U ≫ f) K) ≫ baseChangeMap f (sigmaOpensDesc X U) K) z`. Introduce `p`. Take `⟨i, y, hy⟩` from `sigma_jointly_surjective (fun i => (U i).toScheme) ((baseChangeProjection (sigmaOpensDesc X U ≫ f) K).base p)`. Take `⟨z, hz⟩` from `exists_pullback_snd_base_eq (Sigma.ι (fun i => (U i).toScheme) i) (baseChangeProjection (sigmaOpensDesc X U ≫ f) K) y p hy`.

Conclude with `⟨i, z, hz⟩`.
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

/- English proof (translation)
Establish `: CompactSpace ↥X` using `QuasiCompact.compactSpace_of_compactSpace (f := f)`. Take `⟨ι, hι, U, hUaff, hUtop⟩` from `exists_finite_affine_cover X`. Use `hι` as an intermediate fact. Establish `hWaff : IsAffine (sigmaOpens X U)` using `isAffine_sigmaOpens X U hUaff`. Establish `hsurj : Surjective (sigmaOpensDesc X U)` using `surjective_sigmaOpensDesc X U hUtop`.

Establish `hqc : QuasiCompact (sigmaOpensDesc X U ≫ f)` using `inferInstance`. Establish `hbcaff : IsAffine (baseChange (sigmaOpensDesc X U ≫ f) K)` using `isAffine_baseChange_comp f (sigmaOpensDesc X U) K`. Use `⟨sigmaOpens X U, sigmaOpensDesc X U, baseChangeMap f (sigmaOpensDesc X U) K, hWaff, inferInstance, inferInstance, hqc, inferInstance, hsurj, hbcaff, isReduced_baseChange_sigmaOpensDesc f K U, ?_, ?_, inferInstance, inferInstance, baseChangeMap_comp_baseChangeToSpec f (sigmaOpensD …` and prove the remaining obligations. Conclude with `morphismProperty_of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback (sigmaOpensDesc X U ≫ f) (specMapAlgebraMap k K)).flip inferInstance`. Conclude with `morphismProperty_of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback (sigmaOpensDesc X U ≫ f) (specMapAlgebraMap k K)).flip inferInstance`.
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
