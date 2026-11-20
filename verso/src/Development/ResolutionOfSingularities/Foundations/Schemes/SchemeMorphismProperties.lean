import Mathlib
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace FunctorialResolution.Blowup

/- English proof (translation)
The claim follows from `small_self _`.
-/
private theorem small_directedAffineCover_I₀ (X : Scheme.{u}) :
    Small.{u} X.directedAffineCover.I₀ :=
  small_self _

instance instSmallDirectedAffineCoverI₀ (X : Scheme.{u}) :
    Small.{u} X.directedAffineCover.I₀ :=
  small_directedAffineCover_I₀ X

/- English proof (translation)
Introduce `a b`. Use `⟨fun f g => ?_⟩` and prove the remaining obligations. Take `⟨⟨hf⟩⟩` from `f`. Take `⟨⟨hg⟩⟩` from `g`. Both sides reduce to the same expression.
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

/- English proof (translation)
Establish `h : Topology.IsInducing (fun x : { y : ↥X // y ∈ U } => (x : ↥X))` using `⟨rfl⟩`. Conclude with `h.noetherianSpace`.
-/
theorem noetherianSpace_toScheme (X : Scheme.{u}) [NoetherianSpace ↥X] (U : X.Opens) :
    NoetherianSpace ↥(U.toScheme) := by
  have h : Topology.IsInducing (fun x : { y : ↥X // y ∈ U } => (x : ↥X)) := ⟨rfl⟩
  exact h.noetherianSpace

instance instNoetherianSpaceToScheme (X : Scheme.{u}) [NoetherianSpace ↥X] (U : X.Opens) :
    NoetherianSpace ↥(U.toScheme) :=
  noetherianSpace_toScheme X U

/- English proof (translation)
The claim follows from `inferInstance`.
-/
private theorem isAffineHom_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    AlgebraicGeometry.IsAffineHom (Spec.map φ) :=
  inferInstance

/- English proof (translation)
The claim follows from `MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsAffineHom) (IsPullback.of_hasPullback f g).flip ‹AlgebraicGeometry.IsAffineHom g›`.
-/
private theorem isAffineHom_pullback_fst {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [AlgebraicGeometry.IsAffineHom g] :
    AlgebraicGeometry.IsAffineHom (pullback.fst f g) :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsAffineHom)
    (IsPullback.of_hasPullback f g).flip ‹AlgebraicGeometry.IsAffineHom g›

/- English proof (translation)
The claim follows from `@isAffineHom_pullback_fst X _ _ p (Spec.map φ) (isAffineHom_specMap φ)`.
-/
theorem isAffineHom_pullback_fst_specMap_of_field {k K : Type u} [Field k] [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (φ : CommRingCat.of k ⟶ CommRingCat.of K) :
    AlgebraicGeometry.IsAffineHom (pullback.fst p (Spec.map φ)) :=
  @isAffineHom_pullback_fst X _ _ p (Spec.map φ) (isAffineHom_specMap φ)

instance instIsAffineHomSpecMapPullbackFst {k K : Type u} [Field k] [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (φ : CommRingCat.of k ⟶ CommRingCat.of K) :
    AlgebraicGeometry.IsAffineHom (pullback.fst p (Spec.map φ)) :=
  isAffineHom_pullback_fst_specMap_of_field p φ

/- English proof (translation)
Establish `hmapdef : Z.map ι = Scheme.Hom.ker (Z.subschemeι ≫ ι)` using `rfl`. Establish `hcomapdef : (Z.map ι).comap ι = Scheme.Hom.ker (pullback.fst ι (Z.map ι).subschemeι)` using `rfl`. Establish `hle : Scheme.Hom.ker (Z.subschemeι ≫ ι) ≤ Scheme.Hom.ker (Z.map ι).subschemeι`. Rewrite using `[Scheme.IdealSheafData.ker_subschemeι, ← hmapdef]`. Establish `hu : IsClosedImmersion.lift (Z.subschemeι ≫ ι) (Z.map ι).subschemeι hle ≫ (Z.subschemeι ≫ ι) = (Z.map ι).subschemeι` using `IsClosedImmersion.lift_fac _ _ hle`.

Use `set u := IsClosedImmersion.lift (Z.subschemeι ≫ ι) (Z.map ι).subschemeι hle with hudef`. Establish `hk : (pullback.snd ι (Z.map ι).subschemeι ≫ u) ≫ Z.subschemeι = pullback.fst ι (Z.map ι).subschemeι`. Establish `h2 : ((pullback.snd ι (Z.map ι).subschemeι ≫ u) ≫ Z.subschemeι) ≫ ι = pullback.fst ι (Z.map ι).subschemeι ≫ ι`. Rewrite using `[Category.assoc, Category.assoc, hu]`. Conclude with `pullback.condition.symm`.

Conclude with `(cancel_mono ι).mp h2`. Rewrite using `[hcomapdef, ← hk, Scheme.Hom.ker_comp]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]`. Use `_ ≤ _ := Scheme.IdealSheafData.map_mono Z.subschemeι bot_le`.
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

/- English proof (translation)
The claim follows from `le_antisymm (Scheme.IdealSheafData.comap_map_le Z ι) (le_comap_map_of_isClosedImmersion ι Z)`.
-/
theorem comap_map_of_isClosedImmersion {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] (Z : S.IdealSheafData) :
    (Z.map ι).comap ι = Z :=
  le_antisymm (Scheme.IdealSheafData.comap_map_le Z ι) (le_comap_map_of_isClosedImmersion ι Z)

/- English proof (translation)
Establish `hfin : {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x}.Finite`. Use `Set.Finite.subset (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents) ?_` and prove the remaining obligations. Introduce and unpack `Z ⟨hZ, -⟩`. Conclude with `hZ`. Establish `heq : (connectedComponent x)ᶜ = ⋃ Z ∈ {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x}, Z`.

Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce `y hy`. Conclude with `Set.mem_biUnion (⟨irreducibleComponent_mem_irreducibleComponents y, fun h => hy (h mem_irreducibleComponent)⟩ : irreducibleComponent y ∈ {Z : Set T | Z ∈ irreducibleComponents T ∧ ¬ Z ⊆ connectedComponent x}) mem_irreducibleComponent`. Introduce `z hz`. Simplify using `only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hz`.

Take `⟨Z, ⟨hZ, hZ'⟩, hzZ⟩` from `hz`. Introduce `hzc`. Establish `h1 : Z ⊆ connectedComponent z` using `hZ.1.2.isPreconnected.subset_connectedComponent hzZ`. Rewrite `h1` using `[← connectedComponent_eq hzc]`. Conclude with `hZ' h1`.

Rewrite using `[← isClosed_compl_iff, heq]`. Conclude with `hfin.isClosed_biUnion (fun Z hZ => isClosed_of_mem_irreducibleComponents _ hZ.1)`.
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

/- English proof (translation)
Establish `hfin : (irreducibleComponents Y).Finite` using `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`. Use `Set.Finite.subset (hfin.image fun Z => ⋃ z ∈ Z, connectedComponent z) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Use `⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x, ?_⟩` and prove the remaining obligations. Establish `hsub : irreducibleComponent x ⊆ connectedComponent x` using `(irreducibleComponent_mem_irreducibleComponents x).1.2.isPreconnected.subset_connectedComponent mem_irreducibleComponent`.

Use `show (⋃ z ∈ irreducibleComponent x, connectedComponent z) = connectedComponent x`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce `y hy`. Take `⟨z, hz, hyz⟩` from `Set.mem_iUnion₂.mp hy`. Rewrite `hyz` using `[← connectedComponent_eq (hsub hz)]`. Then use the resulting hypothesis.

Introduce `y hy`. Conclude with `Set.mem_biUnion mem_irreducibleComponent hy`.
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

/- English proof (translation)
Establish `hfin : {C : Set Y | C ∈ Set.range (fun x : Y => connectedComponent x) ∧ C ⊆ A}.Finite`. Use `(finite_range_connectedComponent Y).subset ?_` and prove the remaining obligations. Introduce and unpack `C ⟨hC, -⟩`. Conclude with `hC`. Establish `heq : {x : Y | connectedComponent x ⊆ A} = ⋃ C ∈ {C : Set Y | C ∈ Set.range (fun x : Y => connectedComponent x) ∧ C ⊆ A}, C`.

Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `hmem : connectedComponent x ∈ {C : Set Y | C ∈ Set.range (fun x : Y => connectedComponent x) ∧ C ⊆ A}` using `⟨⟨x, rfl⟩, hx⟩`. Conclude with `Set.mem_biUnion hmem mem_connectedComponent`. Introduce `x hx`.

Take `⟨C, hC, hxC⟩` from `Set.mem_iUnion₂.mp hx`. Take `⟨⟨y, hy⟩, hCA⟩` from `hC`. Establish `hy' : connectedComponent y = C` using `hy`. Rewrite `hxC`, `hCA` using `[← hy']`. Use `show connectedComponent x ⊆ A`.

Rewrite using `[← connectedComponent_eq hxC]`. Conclude with `hCA`. Rewrite using `[heq]`. Use `hfin.isClosed_biUnion ?_` and prove the remaining obligations. Introduce and unpack `C ⟨⟨x, hx⟩, -⟩`.

Establish `hC : C = connectedComponent x` using `hx.symm`. Rewrite using `[hC]`. Conclude with `isClosed_connectedComponent`.
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

/- English proof (translation)
The claim follows from `congrArg X₁.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))`.
-/
theorem presheaf_map_eq_of_parallel (X₁ : Scheme.{u}) {A B : (X₁.Opens)ᵒᵖ} (g₁ g₂ : A ⟶ B) :
    X₁.presheaf.map g₁ = X₁.presheaf.map g₂ :=
  congrArg X₁.presheaf.map (Quiver.Hom.unop_inj (Subsingleton.elim _ _))

namespace Hom

/- English proof (translation)
Substitute `hfg` using the available equality. Both sides reduce to the same expression.
-/
theorem appLE_congr_hom {A B : Scheme.{u}} {f g : A ⟶ B} (hfg : f = g) (O : B.Opens)
    (S : A.Opens) (h1 : S ≤ f ⁻¹ᵁ O) (h2 : S ≤ g ⁻¹ᵁ O) :
    Scheme.Hom.appLE f O S h1 = Scheme.Hom.appLE g O S h2 := by
  subst hfg
  rfl

/- English proof (translation)
Establish `hcomp : ∀ x : A, (f ≫ g).base x = g.base (f.base x)` using `fun _ => rfl`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce and unpack `z ⟨x, rfl⟩`. Conclude with `⟨f.base x, ⟨x, rfl⟩, (hcomp x).symm⟩`. Introduce and unpack `z ⟨y, ⟨x, rfl⟩, rfl⟩`.

Conclude with `⟨x, hcomp x⟩`.
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

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `U _ _`. Break down `Set.eq_empty_or_nonempty (f.base ⁻¹' U) with h | ⟨w, hw⟩` into its components or cases. Rewrite using `[h]`. Conclude with `isCompact_empty`.

Establish `h2 : f.base ⁻¹' U = Set.univ`. Use `Set.eq_univ_of_forall fun w' => ?_` and prove the remaining obligations. Establish `hww : f.base w' = f.base w` using `Subsingleton.elim _ _`. Use `show f.base w' ∈ U`. Rewrite using `[hww]`.

Conclude with `hw`. Rewrite using `[h2]`. Conclude with `isCompact_univ`.
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
