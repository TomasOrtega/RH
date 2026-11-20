import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.IdealSheafOpenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SubschemeMapFlatness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionStepProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.UntwistedDivisorRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BaseChangeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SmoothComponentsDisjoint
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Establish `: TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme` using `noetherianSpace_boundary_subscheme T hV j hj`. Establish `hsd : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩)` using `isSmoothDivisor_boundary_get T hV j hj`. Establish `hsm : AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)` using `((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).mp hsd).2`. Establish `hsep` using `irreducibleComponentsDisjointOfSmooth T.base (T.boundary.get ⟨j, hj⟩).subscheme ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) hsm`. Establish `h1 : connectedComponent z ⊆ irreducibleComponent z` using `connectedComponent_subset_of_mem_irreducibleComponents hsep (irreducibleComponent_mem_irreducibleComponents z) mem_irreducibleComponent`.

Establish `h2 : irreducibleComponent z ⊆ connectedComponent z` using `(isIrreducible_irreducibleComponent (x := z)).2.isPreconnected.subset_connectedComponent mem_irreducibleComponent`. Rewrite using `[Set.Subset.antisymm h1 h2]`. Conclude with `isIrreducible_irreducibleComponent`.
-/
theorem isIrreducible_connectedComponent_boundary_subscheme (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) (z : ↥(T.boundary.get ⟨j, hj⟩).subscheme) :
    IsIrreducible (connectedComponent z) := by
  have : TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    noetherianSpace_boundary_subscheme T hV j hj
  have hsd : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) :=
    isSmoothDivisor_boundary_get T hV j hj
  have hsm : AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    ((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).mp hsd).2
  have hsep := irreducibleComponentsDisjointOfSmooth T.base (T.boundary.get ⟨j, hj⟩).subscheme
    ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) hsm
  have h1 : connectedComponent z ⊆ irreducibleComponent z :=
    connectedComponent_subset_of_mem_irreducibleComponents hsep
      (irreducibleComponent_mem_irreducibleComponents z) mem_irreducibleComponent
  have h2 : irreducibleComponent z ⊆ connectedComponent z :=
    (isIrreducible_irreducibleComponent (x := z)).2.isPreconnected.subset_connectedComponent
      mem_irreducibleComponent
  rw [Set.Subset.antisymm h1 h2]
  exact isIrreducible_irreducibleComponent

/- English proof (translation)
Use `hN` as an intermediate fact. Use `hN'` as an intermediate fact. Conclude with `openSubschemeKer_comap g D A hA ⟨_, hopen⟩ ⟨_, hopen'⟩ rfl rfl (TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset ↥D.subscheme (⇑D.subschemeι.base ⁻¹' A)) (TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset ↥(D.comap g).subscheme (⇑( …`.
-/
theorem openSubschemeKer_comap_of_flat_of_noetherian {X Y : Scheme.{u}} (g : Y ⟶ X)
    [AlgebraicGeometry.Flat g] (D : X.IdealSheafData) (A : Set X) (hA : IsClosed A)
    (hirr : ∀ w : ↥D.subscheme, IsIrreducible (connectedComponent w))
    (hN : TopologicalSpace.NoetherianSpace ↥D.subscheme)
    (hN' : TopologicalSpace.NoetherianSpace ↥(D.comap g).subscheme)
    (hopen : IsOpen {w : ↥D.subscheme | connectedComponent w ⊆ ⇑D.subschemeι.base ⁻¹' A})
    (hopen' : IsOpen {w : ↥(D.comap g).subscheme |
      connectedComponent w ⊆ ⇑(D.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)}) :
    openSubschemeKer (D.comap g)
        ⟨{w : ↥(D.comap g).subscheme |
            connectedComponent w ⊆ ⇑(D.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)}, hopen'⟩ =
      (openSubschemeKer D
        ⟨{w : ↥D.subscheme | connectedComponent w ⊆ ⇑D.subschemeι.base ⁻¹' A}, hopen⟩).comap g := by
  have := hN
  have := hN'
  exact openSubschemeKer_comap g D A hA ⟨_, hopen⟩ ⟨_, hopen'⟩ rfl rfl
    (TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset ↥D.subscheme
      (⇑D.subschemeι.base ⁻¹' A))
    (TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset
      ↥(D.comap g).subscheme
      (⇑(D.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A))) hirr

/- English proof (translation)
Substitute `hF` using the available equality. Simplify using `[List.get_eq_getElem]`.
-/
private theorem get_eq_comap_get_of_eq_map {X Y : Scheme.{u}} (g : Y ⟶ X) (E : List X.IdealSheafData)
    (F : List Y.IdealSheafData) (hF : F = E.map (fun D => D.comap g)) (j : ℕ)
    (hj : j < E.length) (hj' : j < F.length) :
    F.get ⟨j, hj'⟩ = (E.get ⟨j, hj⟩).comap g := by
  subst hF
  simp [List.get_eq_getElem]

/- English proof (translation)
Use `hflat` as an intermediate fact. Establish `hopen` using `isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj`. Establish `hopen'` using `isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T' hV' j hj'`. Establish `hirr : ∀ w : ↥(T.boundary.get ⟨j, hj⟩).subscheme, IsIrreducible (connectedComponent w)` using `fun w => isIrreducible_connectedComponent_boundary_subscheme T hV j hj w`. Establish `hN : TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme` using `noetherianSpace_boundary_subscheme T hV j hj`.

Establish `hN' : TopologicalSpace.NoetherianSpace ↥(T'.boundary.get ⟨j, hj'⟩).subscheme` using `noetherianSpace_boundary_subscheme T' hV' j hj'`. Establish `key : ∀ (D' : T'.scheme.IdealSheafData), D' = (T.boundary.get ⟨j, hj⟩).comap g → ∀ (S' : Set ↥D'.subscheme), S' = {w : ↥D'.subscheme | connectedComponent w ⊆ ⇑D'.subschemeι.base ⁻¹' (⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)} → ∀ (hop' : IsOpen S'), TopologicalSpace.Noetheria …`. Introduce and unpack `D' rfl S' rfl hop' hNN`. Conclude with `openSubschemeKer_comap_of_flat_of_noetherian g (T.boundary.get ⟨j, hj⟩) (orderAtLeastLocus T.ideal T.mult) hcl hirr hN hNN hopen hop'`. Establish `hset : divisorComponentsInOrderLocus T' j hj' = {w : ↥(T'.boundary.get ⟨j, hj'⟩).subscheme | connectedComponent w ⊆ ⇑(T'.boundary.get ⟨j, hj'⟩).subschemeι.base ⁻¹' (⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)}` using `congrArg (fun A : Set ↥T'.scheme => {w : ↥(T'.boundary.get ⟨j, hj'⟩).subscheme | connectedComponent w ⊆ ⇑(T'.boundary.get ⟨j, hj'⟩).subschemeι.base ⁻¹' A}) hcs`.

Rewrite using `[containedComponentsIdeal_eq_openSubschemeKer T j hj hopen, containedComponentsIdeal_eq_openSubschemeKer T' j hj' hopen']`. Conclude with `key _ hD _ hset hopen' hN'`.
-/
private theorem containedComponentsIdeal_comap_of_flat (T T' : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hV' : T'.IsAdmissible) (g : T'.scheme ⟶ T.scheme) (hflat : AlgebraicGeometry.Flat g) (j : ℕ)
    (hj : j < T.boundary.length) (hj' : j < T'.boundary.length)
    (hD : T'.boundary.get ⟨j, hj'⟩ = (T.boundary.get ⟨j, hj⟩).comap g)
    (hcs : orderAtLeastLocus T'.ideal T'.mult = ⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)
    (hcl : IsClosed (orderAtLeastLocus T.ideal T.mult)) :
    DivisorReduction.containedComponentsIdeal T' j hj' = (DivisorReduction.containedComponentsIdeal T j hj).comap g := by
  have := hflat
  have hopen := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj
  have hopen' := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T' hV' j hj'
  have hirr : ∀ w : ↥(T.boundary.get ⟨j, hj⟩).subscheme, IsIrreducible (connectedComponent w) :=
    fun w => isIrreducible_connectedComponent_boundary_subscheme T hV j hj w
  have hN : TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    noetherianSpace_boundary_subscheme T hV j hj
  have hN' : TopologicalSpace.NoetherianSpace ↥(T'.boundary.get ⟨j, hj'⟩).subscheme :=
    noetherianSpace_boundary_subscheme T' hV' j hj'
  have key : ∀ (D' : T'.scheme.IdealSheafData), D' = (T.boundary.get ⟨j, hj⟩).comap g →
      ∀ (S' : Set ↥D'.subscheme),
        S' = {w : ↥D'.subscheme | connectedComponent w ⊆
            ⇑D'.subschemeι.base ⁻¹' (⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)} →
        ∀ (hop' : IsOpen S'), TopologicalSpace.NoetherianSpace ↥D'.subscheme →
          openSubschemeKer D' ⟨S', hop'⟩ =
            (openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, hopen⟩).comap g := by
    rintro D' rfl S' rfl hop' hNN
    exact openSubschemeKer_comap_of_flat_of_noetherian g (T.boundary.get ⟨j, hj⟩)
      (orderAtLeastLocus T.ideal T.mult) hcl hirr hN hNN hopen hop'
  have hset : divisorComponentsInOrderLocus T' j hj' =
      {w : ↥(T'.boundary.get ⟨j, hj'⟩).subscheme | connectedComponent w ⊆
        ⇑(T'.boundary.get ⟨j, hj'⟩).subschemeι.base ⁻¹'
          (⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)} :=
    congrArg (fun A : Set ↥T'.scheme =>
      {w : ↥(T'.boundary.get ⟨j, hj'⟩).subscheme | connectedComponent w ⊆
        ⇑(T'.boundary.get ⟨j, hj'⟩).subschemeι.base ⁻¹' A}) hcs
  rw [containedComponentsIdeal_eq_openSubschemeKer T j hj hopen, containedComponentsIdeal_eq_openSubschemeKer T' j hj' hopen']
  exact key _ hD _ hset hopen' hN'

/- English proof (translation)
Establish `: CharZero T.base` using `hV.charZero`. Establish `: AlgebraicGeometry.Smooth T.structMap` using `hV.smooth`. Establish `hfl : AlgebraicGeometry.Flat h` using `inferInstance`. Establish `hD : (T.pullbackAlong Y q h).boundary.get ⟨j, hj'⟩ = (T.boundary.get ⟨j, hj⟩).comap h` using `get_eq_comap_get_of_eq_map h T.boundary (T.pullbackAlong Y q h).boundary (MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h) j hj hj'`. Establish `hcs : orderAtLeastLocus (T.pullbackAlong Y q h).ideal (T.pullbackAlong Y q h).mult = ⇑h.base ⁻¹' orderAtLeastLocus T.ideal T.mult` using `DivisorReduction.orderAtLeastLocus_comap_of_smooth T hV Y q h hq T.mult`.

Establish `hcl : IsClosed (orderAtLeastLocus T.ideal T.mult)` using `isClosed_orderAtLeastLocus T.base T.structMap T.ideal T.mult`. Conclude with `containedComponentsIdeal_comap_of_flat T (T.pullbackAlong Y q h) hV hV' h hfl j hj hj' hD hcs hcl`.
-/
theorem containedComponentsIdeal_pullbackAlong_of_smooth (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth h]
    (hq : h ≫ T.structMap = q) (hV' : (T.pullbackAlong Y q h).IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (hj' : j < (T.pullbackAlong Y q h).boundary.length) :
    DivisorReduction.containedComponentsIdeal (T.pullbackAlong Y q h) j hj' =
      (DivisorReduction.containedComponentsIdeal T j hj).comap h := by
  have : CharZero T.base := hV.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  have hfl : AlgebraicGeometry.Flat h := inferInstance
  have hD : (T.pullbackAlong Y q h).boundary.get ⟨j, hj'⟩ =
      (T.boundary.get ⟨j, hj⟩).comap h :=
    get_eq_comap_get_of_eq_map h T.boundary (T.pullbackAlong Y q h).boundary
      (MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h) j hj hj'
  have hcs : orderAtLeastLocus (T.pullbackAlong Y q h).ideal (T.pullbackAlong Y q h).mult =
      ⇑h.base ⁻¹' orderAtLeastLocus T.ideal T.mult :=
    DivisorReduction.orderAtLeastLocus_comap_of_smooth T hV Y q h hq T.mult
  have hcl : IsClosed (orderAtLeastLocus T.ideal T.mult) :=
    isClosed_orderAtLeastLocus T.base T.structMap T.ideal T.mult
  exact containedComponentsIdeal_comap_of_flat T (T.pullbackAlong Y q h) hV hV' h hfl j hj hj' hD hcs hcl

/- English proof (translation)
Establish `: CharZero T.base` using `hV.charZero`. Establish `: AlgebraicGeometry.Smooth T.structMap` using `hV.smooth`. Establish `hfl : AlgebraicGeometry.Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f))` using `flat_fieldBaseChangeProjection T L f`. Establish `hD : (T.baseChange L f).boundary.get ⟨j, hj'⟩ = (T.boundary.get ⟨j, hj⟩).comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f))` using `get_eq_comap_get_of_eq_map (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) T.boundary (T.baseChange L f).boundary (MarkedIdealWithBoundary.baseChange_boundary T L f) j hj hj'`. Establish `hcs : orderAtLeastLocus (T.baseChange L f).ideal (T.baseChange L f).mult = ⇑(pullback.fst T.structMap (specMapOfFieldHom T.base L f)).base ⁻¹' orderAtLeastLocus T.ideal T.mult` using `orderAtLeastLocus_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal T.mult`.

Establish `hcl : IsClosed (orderAtLeastLocus T.ideal T.mult)` using `isClosed_orderAtLeastLocus T.base T.structMap T.ideal T.mult`. Conclude with `containedComponentsIdeal_comap_of_flat T (T.baseChange L f) hV hV' (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) hfl j hj hj' hD hcs hcl`.
-/
theorem containedComponentsIdeal_baseChange (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (L : Type u) [Field L]
    [CharZero L] (f : T.base →+* L) (hV' : (T.baseChange L f).IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (hj' : j < (T.baseChange L f).boundary.length) :
    DivisorReduction.containedComponentsIdeal (T.baseChange L f) j hj' =
      (DivisorReduction.containedComponentsIdeal T j hj).comap
        (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) := by
  have : CharZero T.base := hV.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  have hfl : AlgebraicGeometry.Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    flat_fieldBaseChangeProjection T L f
  have hD : (T.baseChange L f).boundary.get ⟨j, hj'⟩ =
      (T.boundary.get ⟨j, hj⟩).comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    get_eq_comap_get_of_eq_map (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) T.boundary
      (T.baseChange L f).boundary (MarkedIdealWithBoundary.baseChange_boundary T L f) j hj hj'
  have hcs : orderAtLeastLocus (T.baseChange L f).ideal (T.baseChange L f).mult =
      ⇑(pullback.fst T.structMap (specMapOfFieldHom T.base L f)).base ⁻¹'
        orderAtLeastLocus T.ideal T.mult :=
    orderAtLeastLocus_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal T.mult
  have hcl : IsClosed (orderAtLeastLocus T.ideal T.mult) :=
    isClosed_orderAtLeastLocus T.base T.structMap T.ideal T.mult
  exact containedComponentsIdeal_comap_of_flat T (T.baseChange L f) hV hV'
    (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) hfl j hj hj' hD hcs hcl

end FunctorialResolution.EmbeddedResolution

end
