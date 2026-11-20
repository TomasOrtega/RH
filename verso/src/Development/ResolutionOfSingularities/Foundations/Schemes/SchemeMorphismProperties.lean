import Mathlib
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace FunctorialResolution.Blowup

/- English proof (authored)
The indexing type for the directed affine cover already lies in the specified universe, so it is small in that universe.
-/
private theorem small_directedAffineCover_I₀ (X : Scheme.{u}) :
    Small.{u} X.directedAffineCover.I₀ :=
  small_self _

instance instSmallDirectedAffineCoverI₀ (X : Scheme.{u}) :
    Small.{u} X.directedAffineCover.I₀ :=
  small_directedAffineCover_I₀ X

/- English proof (authored)
Morphisms in the index category record the order relation of the opens. Between two fixed opens they are proofs of the same inclusion, so any two such morphisms coincide.
-/
private theorem isThin_directedAffineCover_I₀ (X : Scheme.{u}) :
    Quiver.IsThin X.directedAffineCover.I₀ := by
  intro a b
  refine ⟨fun f g => ?_⟩
  obtain ⟨⟨hf⟩⟩ := f
  obtain ⟨⟨hg⟩⟩ := g
  rfl

instance instIsThinDirectedAffineCoverI₀ (X : Scheme.{u}) :
    Quiver.IsThin X.directedAffineCover.I₀ :=
  isThin_directedAffineCover_I₀ X

/- English proof (authored)
The open subscheme has the topology induced by its inclusion into the original scheme. Subspaces of Noetherian spaces are Noetherian.
-/
theorem noetherianSpace_toScheme (X : Scheme.{u}) [NoetherianSpace ↥X] (U : X.Opens) :
    NoetherianSpace ↥(U.toScheme) := by
  have h : Topology.IsInducing (fun x : { y : ↥X // y ∈ U } => (x : ↥X)) := ⟨rfl⟩
  exact h.noetherianSpace

instance instNoetherianSpaceToScheme (X : Scheme.{u}) [NoetherianSpace ↥X] (U : X.Opens) :
    NoetherianSpace ↥(U.toScheme) :=
  noetherianSpace_toScheme X U

/- English proof (authored)
A ring homomorphism gives the corresponding map of affine spectra. Its inverse image of a basic open is the spectrum of the corresponding localization, so the morphism is affine.
-/
private theorem isAffineHom_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    AlgebraicGeometry.IsAffineHom (Spec.map φ) :=
  inferInstance

/- English proof (authored)
The first projection in the pullback square is a base change of the affine map. Affineness is stable under base change.
-/
private theorem isAffineHom_pullback_fst {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [AlgebraicGeometry.IsAffineHom g] :
    AlgebraicGeometry.IsAffineHom (pullback.fst f g) :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsAffineHom)
    (IsPullback.of_hasPullback f g).flip ‹AlgebraicGeometry.IsAffineHom g›

/- English proof (authored)
The map of spectra induced by the field homomorphism is affine. The indicated first projection is its base change, so it is affine as well.
-/
theorem isAffineHom_pullback_fst_specMap_of_field {k K : Type u} [Field k] [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (φ : CommRingCat.of k ⟶ CommRingCat.of K) :
    AlgebraicGeometry.IsAffineHom (pullback.fst p (Spec.map φ)) :=
  @isAffineHom_pullback_fst X _ _ p (Spec.map φ) (isAffineHom_specMap φ)

instance instIsAffineHomSpecMapPullbackFst {k K : Type u} [Field k] [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (φ : CommRingCat.of k ⟶ CommRingCat.of K) :
    AlgebraicGeometry.IsAffineHom (pullback.fst p (Spec.map φ)) :=
  isAffineHom_pullback_fst_specMap_of_field p φ

/- English proof (authored)
The image ideal is the kernel of the closed-subscheme inclusion followed by the given closed immersion. This kernel identifies the closed subscheme of the image ideal with a subscheme factoring through that composite, by the universal property of the closed immersion. In the pullback defining the inverse image ideal, compose the projection to this image subscheme with that factorization. The resulting map to the original closed subscheme followed by its inclusion agrees with the pullback projection to the original ambient scheme, because both agree after composing with the given monomorphism. The kernel of the projection therefore contains the kernel of the original closed-subscheme inclusion, which is the original ideal.
-/
private theorem le_comap_map_of_isClosedImmersion {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] (Z : S.IdealSheafData) : Z ≤ (Z.map ι).comap ι := by
  have hmapdef : Z.map ι = Scheme.Hom.ker (Z.subschemeι ≫ ι) := rfl
  have hcomapdef : (Z.map ι).comap ι
      = Scheme.Hom.ker (pullback.fst ι (Z.map ι).subschemeι) := rfl
  have hle : Scheme.Hom.ker (Z.subschemeι ≫ ι)
      ≤ Scheme.Hom.ker (Z.map ι).subschemeι := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← hmapdef]
  have hu : IsClosedImmersion.lift (Z.subschemeι ≫ ι) (Z.map ι).subschemeι hle
      ≫ (Z.subschemeι ≫ ι) = (Z.map ι).subschemeι :=
    IsClosedImmersion.lift_fac _ _ hle
  set u := IsClosedImmersion.lift (Z.subschemeι ≫ ι) (Z.map ι).subschemeι hle with hudef
  have hk : (pullback.snd ι (Z.map ι).subschemeι ≫ u) ≫ Z.subschemeι
      = pullback.fst ι (Z.map ι).subschemeι := by
    have h2 : ((pullback.snd ι (Z.map ι).subschemeι ≫ u) ≫ Z.subschemeι) ≫ ι
        = pullback.fst ι (Z.map ι).subschemeι ≫ ι := by
      rw [Category.assoc, Category.assoc, hu]
      exact pullback.condition.symm
    exact (cancel_mono ι).mp h2
  rw [hcomapdef, ← hk, Scheme.Hom.ker_comp]
  calc Z = (⊥ : Z.subscheme.IdealSheafData).map Z.subschemeι := by
        rw [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]
    _ ≤ _ := Scheme.IdealSheafData.map_mono Z.subschemeι bot_le

/- English proof (authored)
The general image and pullback inequality gives one containment. The factorization through the original closed subscheme for a closed immersion gives the reverse containment, proving equality.
-/
theorem comap_map_of_isClosedImmersion {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] (Z : S.IdealSheafData) :
    (Z.map ι).comap ι = Z :=
  le_antisymm (Scheme.IdealSheafData.comap_map_le Z ι) (le_comap_map_of_isClosedImmersion ι Z)

/- English proof (authored)
There are finitely many irreducible components, each closed. Since an irreducible component is connected, any one meeting the given connected component lies entirely in it. Every point outside belongs to some irreducible component disjoint from it. Thus the complement is the union of the finitely many irreducible components outside it. This is closed, so the connected component is open.
-/
theorem isOpen_connectedComponent_of_noetherianSpace (T : Type v) [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] (x : T) : IsOpen (connectedComponent x) := by
  classical
  have hfin : {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x}.Finite := by
    refine Set.Finite.subset
      (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents) ?_
    rintro Z ⟨hZ, -⟩
    exact hZ
  have heq : (connectedComponent x)ᶜ
      = ⋃ Z ∈ {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x}, Z := by
    apply Set.Subset.antisymm
    · intro y hy
      exact Set.mem_biUnion
        (⟨irreducibleComponent_mem_irreducibleComponents y,
          fun h => hy (h mem_irreducibleComponent)⟩ :
          irreducibleComponent y ∈
            {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x})
        mem_irreducibleComponent
    · intro z hz
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hz
      obtain ⟨Z, ⟨hZ, hZ'⟩, hzZ⟩ := hz
      intro hzc
      have h1 : Z ⊆ connectedComponent z :=
        hZ.1.2.isPreconnected.subset_connectedComponent hzZ
      rw [← connectedComponent_eq hzc] at h1
      exact hZ' h1
  rw [← isClosed_compl_iff, heq]
  exact hfin.isClosed_biUnion (fun Z hZ => isClosed_of_mem_irreducibleComponents _ hZ.1)

end FunctorialResolution.Blowup

namespace TopologicalSpace.NoetherianSpace

/- English proof (authored)
Every point belongs to an irreducible component, which is connected and therefore contained in the point's connected component. For each irreducible component, take the union of the connected components of its points. This equals the connected component of any one of its points. Every connected component is obtained this way from one of finitely many irreducible components.
-/
theorem finite_range_connectedComponent (Y : Type*) [TopologicalSpace Y] [NoetherianSpace Y] :
    (Set.range fun x : Y => connectedComponent x).Finite := by
  classical
  have hfin : (irreducibleComponents Y).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  refine Set.Finite.subset (hfin.image fun Z => ⋃ z ∈ Z, connectedComponent z) ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x, ?_⟩
  have hsub : irreducibleComponent x ⊆ connectedComponent x :=
    (irreducibleComponent_mem_irreducibleComponents x).1.2.isPreconnected.subset_connectedComponent
      mem_irreducibleComponent
  show (⋃ z ∈ irreducibleComponent x, connectedComponent z) = connectedComponent x
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp hy
    rwa [← connectedComponent_eq (hsub hz)] at hyz
  · intro y hy
    exact Set.mem_biUnion mem_irreducibleComponent hy

/- English proof (authored)
The set is the union of the connected components that lie within the given set. Membership in one such component is equivalent to having it as one's own component. There are finitely many components, each closed, so this union is closed.
-/
theorem isClosed_setOf_connectedComponent_subset (Y : Type*) [TopologicalSpace Y]
    [NoetherianSpace Y] (A : Set Y) : IsClosed {x : Y | connectedComponent x ⊆ A} := by
  classical
  have hfin :
      {C : Set Y | C ∈ Set.range (fun x : Y => connectedComponent x) ∧ C ⊆ A}.Finite := by
    refine (finite_range_connectedComponent Y).subset ?_
    rintro C ⟨hC, -⟩
    exact hC
  have heq : {x : Y | connectedComponent x ⊆ A}
      = ⋃ C ∈ {C : Set Y | C ∈ Set.range (fun x : Y => connectedComponent x) ∧ C ⊆ A}, C := by
    apply Set.Subset.antisymm
    · intro x hx
      have hmem : connectedComponent x ∈
          {C : Set Y | C ∈ Set.range (fun x : Y => connectedComponent x) ∧ C ⊆ A} :=
        ⟨⟨x, rfl⟩, hx⟩
      exact Set.mem_biUnion hmem mem_connectedComponent
    · intro x hx
      obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨⟨y, hy⟩, hCA⟩ := hC
      have hy' : connectedComponent y = C := hy
      rw [← hy'] at hxC hCA
      show connectedComponent x ⊆ A
      rw [← connectedComponent_eq hxC]
      exact hCA
  rw [heq]
  refine hfin.isClosed_biUnion ?_
  rintro C ⟨⟨x, hx⟩, -⟩
  have hC : C = connectedComponent x := hx.symm
  rw [hC]
  exact isClosed_connectedComponent

end TopologicalSpace.NoetherianSpace

namespace AlgebraicGeometry

namespace Scheme

/- English proof (authored)
The category of opens is a poset category, so parallel morphisms in its opposite category are equal. Applying the presheaf to this equality gives equality of the restriction maps.
-/
theorem presheaf_map_eq_of_parallel (X₁ : Scheme.{u}) {A B : (X₁.Opens)ᵒᵖ} (g₁ g₂ : A ⟶ B) :
    X₁.presheaf.map g₁ = X₁.presheaf.map g₂ :=
  congrArg X₁.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

namespace Hom

/- English proof (authored)
After identifying the morphisms, the opens and the inclusion condition are the same. Their induced restricted maps on sections therefore agree.
-/
theorem appLE_congr_hom {A B : Scheme.{u}} {f g : A ⟶ B} (hfg : f = g) (O : B.Opens)
    (S : A.Opens) (h1 : S ≤ f ⁻¹ᵁ O) (h2 : S ≤ g ⁻¹ᵁ O) :
    Scheme.Hom.appLE f O S h1 = Scheme.Hom.appLE g O S h2 := by
  subst hfg
  rfl

/- English proof (authored)
A point of the composite range is obtained by applying the second map to an image point of the first map. Conversely, a point in the second image of the first range is obtained from a point of the first source, so lies in the range of the composite.
-/
theorem range_comp_base {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range (f ≫ g).base = g.base '' Set.range f.base := by
  have hcomp : ∀ x : A, (f ≫ g).base x = g.base (f.base x) := fun _ => rfl
  apply Set.Subset.antisymm
  · rintro z ⟨x, rfl⟩
    exact ⟨f.base x, ⟨x, rfl⟩, (hcomp x).symm⟩
  · rintro z ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, hcomp x⟩

end Hom

end Scheme

/- English proof (authored)
The inverse image of any open in a target with at most one point is empty or the whole source. The former is quasi-compact, and the latter is quasi-compact by the given hypothesis. This is the quasi-compactness condition for the morphism.
-/
theorem quasiCompact_of_compactSpace_of_subsingleton {W S : Scheme.{u}} (f : W ⟶ S)
    [CompactSpace ↥W] [Subsingleton ↥S] : QuasiCompact f := by
  constructor
  intro U _ _
  rcases Set.eq_empty_or_nonempty (f.base ⁻¹' U) with h | ⟨w, hw⟩
  · rw [h]
    exact isCompact_empty
  · have h2 : f.base ⁻¹' U = Set.univ := by
      refine Set.eq_univ_of_forall fun w' => ?_
      have hww : f.base w' = f.base w := Subsingleton.elim _ _
      show f.base w' ∈ U
      rw [hww]
      exact hw
    rw [h2]
    exact isCompact_univ

end AlgebraicGeometry
