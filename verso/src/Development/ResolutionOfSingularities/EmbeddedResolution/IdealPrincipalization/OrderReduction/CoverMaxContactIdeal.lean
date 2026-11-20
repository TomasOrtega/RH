import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMapSurjective
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.PolynomialCoordinateExtension
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Rewrite using `[Category.assoc, c.comp_struct, ← Category.assoc, morphismRestrict_ι, Category.assoc]`.
-/
private theorem comapEtale_map_comp_affineSpaceFinToSpec {k : Type u} [Field k] {X Y : Scheme.{u}}
    {q : Y ⟶ Spec (CommRingCat.of k)} (g : X ⟶ Y) {U : Y.Opens} {n : ℕ}
    (c : EtaleChart q U n) :
    (morphismRestrict g U ≫ c.map) ≫ affineSpaceFinToSpec k n =
      AlgebraicGeometry.Scheme.Opens.ι ((TopologicalSpace.Opens.map g.base).obj U) ≫ (g ≫ q) := by
  rw [Category.assoc, c.comp_struct, ← Category.assoc, morphismRestrict_ι, Category.assoc]

/- English proof (translation)
Use `c.isEtale` as an intermediate fact. Use `infer_instance`.
-/
private theorem etale_comapEtale_map {k : Type u} [Field k] {X Y : Scheme.{u}}
    {q : Y ⟶ Spec (CommRingCat.of k)} (g : X ⟶ Y) [AlgebraicGeometry.Etale g]
    {U : Y.Opens} {n : ℕ} (c : EtaleChart q U n) :
    AlgebraicGeometry.Etale (morphismRestrict g U ≫ c.map) := by
  have := c.isEtale
  infer_instance

def EtaleChart.comapEtale {k : Type u} [Field k] {X Y : Scheme.{u}}
    {q : Y ⟶ Spec (CommRingCat.of k)} (g : X ⟶ Y) [AlgebraicGeometry.Etale g]
    {U : Y.Opens} {n : ℕ} (c : EtaleChart q U n) :
    EtaleChart (g ≫ q) ((TopologicalSpace.Opens.map g.base).obj U) n where
  map := morphismRestrict g U ≫ c.map
  comp_struct := comapEtale_map_comp_affineSpaceFinToSpec g c
  isEtale := etale_comapEtale_map g c

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem EtaleChart.comapEtale_map {k : Type u} [Field k] {X Y : Scheme.{u}}
    {q : Y ⟶ Spec (CommRingCat.of k)} (g : X ⟶ Y) [AlgebraicGeometry.Etale g]
    {U : Y.Opens} {n : ℕ} (c : EtaleChart q U n) :
    (EtaleChart.comapEtale g c).map = morphismRestrict g U ≫ c.map := rfl

/- English proof (translation)
The claim follows from `(Scheme.Opens.range_ι U).subset`.
-/
private theorem range_ι_base_subset {X : Scheme.{u}} (U : X.Opens) :
    Set.range U.ι.base ⊆ (U : Set ↥X) :=
  (Scheme.Opens.range_ι U).subset

/- English proof (translation)
Establish `h1 : (I.comap b).comap a = I.comap (a ≫ b)`. Simplify using `[Scheme.IdealSheafData.comap_comp]`. Establish `h2 : (I.comap b').comap a' = I.comap (a' ≫ b')`. Simplify using `[Scheme.IdealSheafData.comap_comp]`. Rewrite using `[h1, h2, hsq]`.
-/
private theorem comap_comap_eq_of_comp_eq {W X Y Z : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ Z) (a' : W ⟶ Y)
    (b' : Y ⟶ Z) (hsq : a ≫ b = a' ≫ b') (I : Z.IdealSheafData) :
    (I.comap b).comap a = (I.comap b').comap a' := by
  have h1 : (I.comap b).comap a = I.comap (a ≫ b) := by
    simp [Scheme.IdealSheafData.comap_comp]
  have h2 : (I.comap b').comap a' = I.comap (a' ≫ b') := by
    simp [Scheme.IdealSheafData.comap_comp]
  rw [h1, h2, hsq]

/- English proof (translation)
The claim follows from `(MaxContactOpenCover.restrictIdeal_coverTripleOpen T hv i (MaxContactCoverData.coverMaxContactIdeal T hv)).trans (congrArg (fun J : (MaxContactOpenCover.coverPiece T hv i).IdealSheafData => J.comap (MaxContactOpenCover.coverPieceIso T hv i).inv) (hres i))`.
-/
private theorem restrictIdeal_coverTripleOpen_coverMaxContactIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hres : ∀ i : (MaxContactCoverData.chosenCoverData T hv).idx,
      (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
        (MaxContactCoverData.chosenCoverData T hv).localIdeal i)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    @restrictIdeal (MaxContactCoverData.coverTriple T hv).scheme
        (MaxContactCoverData.coverMaxContactIdeal T hv) (MaxContactOpenCover.coverTripleOpen T hv i) =
      ((MaxContactCoverData.chosenCoverData T hv).localIdeal i).comap (MaxContactOpenCover.coverPieceIso T hv i).inv :=
  (MaxContactOpenCover.restrictIdeal_coverTripleOpen T hv i (MaxContactCoverData.coverMaxContactIdeal T hv)).trans
    (congrArg (fun J : (MaxContactOpenCover.coverPiece T hv i).IdealSheafData =>
      J.comap (MaxContactOpenCover.coverPieceIso T hv i).inv) (hres i))

/- English proof (translation)
Use `hv.charZero` as an intermediate fact. Use `hv.smooth` as an intermediate fact. Use `hv.locallyOfFiniteType` as an intermediate fact. Establish `hftc : AlgebraicGeometry.LocallyOfFiniteType (MaxContactCoverData.coverMap T hv ≫ T.structMap)` using `(inferInstance : AlgebraicGeometry.LocallyOfFiniteType (MaxContactCoverData.coverTriple T hv).structMap)`. Introduce `x`.

Take `⟨i, hxi⟩` from `MaxContactOpenCover.exists_mem_coverTripleOpen T hv x`. Establish `hAff0 : AlgebraicGeometry.IsAffine (MaxContactOpenCover.coverPiece T hv i)` using `hgood.isAffine i`. Establish `haffineOpen : IsAffineOpen (MaxContactOpenCover.coverTripleOpen T hv i)` using `isAffineOpen_opensRange (MaxContactOpenCover.coverPieceι T hv i)`. Use `⟨MaxContactOpenCover.coverTripleOpen T hv i, haffineOpen, hxi, ?_⟩` and prove the remaining obligations. Establish `hcompι : MaxContactOpenCover.coverPieceι T hv i ≫ MaxContactCoverData.coverMap T hv = ((MaxContactCoverData.chosenCoverData T hv).opens i).ι` using `sigma_ι_sigmaOpensDesc T.scheme (MaxContactCoverData.chosenCoverData T hv).opens i`.

Establish `hsub : ∀ y : ↥(MaxContactCoverData.coverTriple T hv).scheme, y ∈ (↑(MaxContactOpenCover.coverTripleOpen T hv i) : Set ↥(MaxContactCoverData.coverTriple T hv).scheme) → (MaxContactCoverData.coverMap T hv).base y ∈ (↑((MaxContactCoverData.chosenCoverData T hv).opens i) : Set ↥T.sch …`. Introduce `y hy`. Establish `hy' : y ∈ Set.range (MaxContactOpenCover.coverPieceι T hv i).base` using `hy`. Take `⟨z, rfl⟩` from `hy'`. Establish `hz : (MaxContactCoverData.coverMap T hv).base ((MaxContactOpenCover.coverPieceι T hv i).base z) = ((MaxContactCoverData.chosenCoverData T hv).opens i).ι.base z`.

Rewrite using `[← hcompι]`. Both sides reduce to the same expression. Rewrite using `[hz]`. Conclude with `range_ι_base_subset _ ⟨z, rfl⟩`. Break down `hgood.dichotomy i with ⟨hdisj, htop⟩ | ⟨n, c, j, hloc, hmc⟩` into its components or cases.

Use `left`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.disjoint_left]`. Introduce `y hy hy2`. Establish `hy3 : y ∈ orderAtLeastLocus ((MaxContactCoverData.balancedTunedIdeal T hv).comap (MaxContactCoverData.coverMap T hv)) (MaxContactCoverData.tunedMult T)` using `hy`.

Rewrite `hy3` using `[orderAtLeastLocus_comap T.base T.structMap (MaxContactCoverData.coverMap T hv) (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)]`. Establish `hy4 : (MaxContactCoverData.coverMap T hv).base y ∈ orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)` using `hy3`. Conclude with `(Set.disjoint_left.mp hdisj) hy4 (hsub y hy2)`. Rewrite using `[restrictIdeal_coverTripleOpen_coverMaxContactIdeal T hv hres i, htop]`. Conclude with `Scheme.IdealSheafData.comap_top _`.

Use `right`. Use `⟨n, MaxContactOpenCover.coverEtaleChart T hv i c, j, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[restrictIdeal_coverTripleOpen_coverMaxContactIdeal T hv hres i, hloc]`. Conclude with `(MaxContactOpenCover.coverEtaleChart_coordIdeal T hv i c {j}).symm`. Establish `hmc' : c.coordIdeal {j} ≤ (maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)).comap ((MaxContactCoverData.chosenCoverData T hv).opens i).ι` using `hmc`.

Establish `hmax : maxContactIdeal (MaxContactCoverData.coverTriple T hv).base (MaxContactCoverData.coverTriple T hv).structMap (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.tunedMult T) = (maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv) ( …` using `derivIdealSheafIterate_comap T.base T.structMap (MaxContactCoverData.coverMap T hv) (MaxContactCoverData.tunedMult T - 1) (MaxContactCoverData.balancedTunedIdeal T hv)`. Establish `h1 : (MaxContactOpenCover.coverEtaleChart T hv i c).coordIdeal {j} = (c.coordIdeal {j}).comap (MaxContactOpenCover.coverPieceIso T hv i).inv` using `MaxContactOpenCover.coverEtaleChart_coordIdeal T hv i c {j}`. Establish `h2` using `comap_comap_eq_of_comp_eq (MaxContactOpenCover.coverTripleOpen T hv i).ι (MaxContactCoverData.coverMap T hv) (MaxContactOpenCover.coverPieceIso T hv i).inv ((MaxContactCoverData.chosenCoverData T hv).opens i).ι (MaxContactOpenCover.coverTripleOpen_ι_comp_coverMap T hv i) (maxCont …`. Establish `h3 : (c.coordIdeal {j}).comap (MaxContactOpenCover.coverPieceIso T hv i).inv ≤ ((maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)).comap ((MaxContactCoverData.chosenCoverData T hv).opens i).ι).comap (MaxContactOpen …` using `Scheme.IdealSheafData.comap_mono _ hmc'`. Use `show (MaxContactOpenCover.coverEtaleChart T hv i c).coordIdeal {j} ≤ restrictIdeal (maxContactIdeal (MaxContactCoverData.coverTriple T hv).base (MaxContactCoverData.coverTriple T hv).structMap (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.tunedMult T)) (MaxCon …`.

Rewrite using `[hmax]`. Conclude with `(le_of_eq h1).trans (le_of_le_of_eq h3 h2.symm)`.
-/
theorem isMaxContactHypersurface_coverMaxContactIdeal_of_comap_eq (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    [AlgebraicGeometry.LocallyOfFiniteType (MaxContactCoverData.coverTriple T hv).structMap]
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
    (hres : ∀ i : (MaxContactCoverData.chosenCoverData T hv).idx,
      (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
        (MaxContactCoverData.chosenCoverData T hv).localIdeal i) :
    IsMaxContactHypersurface (MaxContactCoverData.coverTriple T hv).base
      (MaxContactCoverData.coverTriple T hv).structMap (MaxContactCoverData.coverTriple T hv).ideal
      (MaxContactCoverData.tunedMult T) (MaxContactCoverData.coverMaxContactIdeal T hv) := by
  have := hv.charZero
  have := hv.smooth
  have := hv.locallyOfFiniteType
  have hftc : AlgebraicGeometry.LocallyOfFiniteType
      (MaxContactCoverData.coverMap T hv ≫ T.structMap) :=
    (inferInstance : AlgebraicGeometry.LocallyOfFiniteType
      (MaxContactCoverData.coverTriple T hv).structMap)
  intro x
  obtain ⟨i, hxi⟩ := MaxContactOpenCover.exists_mem_coverTripleOpen T hv x
  have hAff0 : AlgebraicGeometry.IsAffine (MaxContactOpenCover.coverPiece T hv i) := hgood.isAffine i
  have haffineOpen : IsAffineOpen (MaxContactOpenCover.coverTripleOpen T hv i) :=
    isAffineOpen_opensRange (MaxContactOpenCover.coverPieceι T hv i)
  refine ⟨MaxContactOpenCover.coverTripleOpen T hv i, haffineOpen, hxi, ?_⟩
  have hcompι : MaxContactOpenCover.coverPieceι T hv i ≫ MaxContactCoverData.coverMap T hv =
      ((MaxContactCoverData.chosenCoverData T hv).opens i).ι :=
    sigma_ι_sigmaOpensDesc T.scheme (MaxContactCoverData.chosenCoverData T hv).opens i
  have hsub : ∀ y : ↥(MaxContactCoverData.coverTriple T hv).scheme,
      y ∈ (↑(MaxContactOpenCover.coverTripleOpen T hv i) :
        Set ↥(MaxContactCoverData.coverTriple T hv).scheme) →
      (MaxContactCoverData.coverMap T hv).base y ∈
        (↑((MaxContactCoverData.chosenCoverData T hv).opens i) : Set ↥T.scheme) := by
    intro y hy
    have hy' : y ∈ Set.range (MaxContactOpenCover.coverPieceι T hv i).base := hy
    obtain ⟨z, rfl⟩ := hy'
    have hz : (MaxContactCoverData.coverMap T hv).base ((MaxContactOpenCover.coverPieceι T hv i).base z) =
        ((MaxContactCoverData.chosenCoverData T hv).opens i).ι.base z := by
      rw [← hcompι]
      rfl
    rw [hz]
    exact range_ι_base_subset _ ⟨z, rfl⟩
  rcases hgood.dichotomy i with ⟨hdisj, htop⟩ | ⟨n, c, j, hloc, hmc⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      intro y hy hy2
      have hy3 : y ∈ orderAtLeastLocus
          ((MaxContactCoverData.balancedTunedIdeal T hv).comap (MaxContactCoverData.coverMap T hv))
          (MaxContactCoverData.tunedMult T) := hy
      rw [orderAtLeastLocus_comap T.base T.structMap (MaxContactCoverData.coverMap T hv)
        (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)] at hy3
      have hy4 : (MaxContactCoverData.coverMap T hv).base y ∈
          orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) := hy3
      exact (Set.disjoint_left.mp hdisj) hy4 (hsub y hy2)
    · rw [restrictIdeal_coverTripleOpen_coverMaxContactIdeal T hv hres i, htop]
      exact Scheme.IdealSheafData.comap_top _
  · right
    refine ⟨n, MaxContactOpenCover.coverEtaleChart T hv i c, j, ?_, ?_⟩
    · rw [restrictIdeal_coverTripleOpen_coverMaxContactIdeal T hv hres i, hloc]
      exact (MaxContactOpenCover.coverEtaleChart_coordIdeal T hv i c {j}).symm
    · have hmc' : c.coordIdeal {j} ≤
          (maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv)
            (MaxContactCoverData.tunedMult T)).comap
            ((MaxContactCoverData.chosenCoverData T hv).opens i).ι := hmc
      have hmax : maxContactIdeal (MaxContactCoverData.coverTriple T hv).base
            (MaxContactCoverData.coverTriple T hv).structMap
            (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.tunedMult T) =
          (maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv)
            (MaxContactCoverData.tunedMult T)).comap (MaxContactCoverData.coverMap T hv) :=
        derivIdealSheafIterate_comap T.base T.structMap (MaxContactCoverData.coverMap T hv)
          (MaxContactCoverData.tunedMult T - 1) (MaxContactCoverData.balancedTunedIdeal T hv)
      have h1 : (MaxContactOpenCover.coverEtaleChart T hv i c).coordIdeal {j}
          = (c.coordIdeal {j}).comap (MaxContactOpenCover.coverPieceIso T hv i).inv :=
        MaxContactOpenCover.coverEtaleChart_coordIdeal T hv i c {j}
      have h2 := comap_comap_eq_of_comp_eq (MaxContactOpenCover.coverTripleOpen T hv i).ι
        (MaxContactCoverData.coverMap T hv)
        (MaxContactOpenCover.coverPieceIso T hv i).inv ((MaxContactCoverData.chosenCoverData T hv).opens i).ι
        (MaxContactOpenCover.coverTripleOpen_ι_comp_coverMap T hv i)
        (maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv)
          (MaxContactCoverData.tunedMult T))
      have h3 : (c.coordIdeal {j}).comap (MaxContactOpenCover.coverPieceIso T hv i).inv ≤
          ((maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv)
            (MaxContactCoverData.tunedMult T)).comap
              ((MaxContactCoverData.chosenCoverData T hv).opens i).ι).comap
            (MaxContactOpenCover.coverPieceIso T hv i).inv :=
        Scheme.IdealSheafData.comap_mono _ hmc'
      show (MaxContactOpenCover.coverEtaleChart T hv i c).coordIdeal {j} ≤
        restrictIdeal (maxContactIdeal (MaxContactCoverData.coverTriple T hv).base
          (MaxContactCoverData.coverTriple T hv).structMap
          (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.tunedMult T))
          (MaxContactOpenCover.coverTripleOpen T hv i)
      rw [hmax]
      exact (le_of_eq h1).trans (le_of_le_of_eq h3 h2.symm)

/- English proof (translation)
Take `⟨i, hxi⟩` from `MaxContactOpenCover.exists_mem_coverTripleOpen T hv x`. Establish `h1` using `MaxContactOpenCover.restrictIdeal_coverTripleOpen T hv i (MaxContactCoverData.coverMaxContactIdeal T hv)`. Break down `hgood.dichotomy i with ⟨_hdisj, htop⟩ | ⟨n, c, j, hlocal, _hmc⟩` into its components or cases. Establish `h2 : ((MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i)).comap (MaxContactOpenCover.coverPieceIso T hv i).inv = ⊤`. Rewrite using `[hres i, htop]`.

Conclude with `Scheme.IdealSheafData.comap_top _`. Establish `key` using `h1.trans h2`. Establish `hsm : AlgebraicGeometry.Smooth (MaxContactCoverData.coverTriple T hv).structMap`. Use `MaxContactCoverData.smooth_coverMap_of_isAdmissible T hv` as an intermediate fact. Use `hv.smooth` as an intermediate fact.

Conclude with `(inferInstance : AlgebraicGeometry.Smooth (MaxContactCoverData.coverMap T hv ≫ T.structMap))`. Take `⟨U, m, hxU, hUle, -, ⟨ch⟩⟩` from `exists_etaleChart_le (MaxContactCoverData.coverTriple T hv).structMap x (MaxContactOpenCover.coverTripleOpen T hv i) hxi`. Establish `keyU : restrictIdeal (MaxContactCoverData.coverMaxContactIdeal T hv) U = ⊤`. Apply the tactic sequence `apply restrictIdeal_eq_top_of_le <;> assumption`. Use `inStrictNormalCrossingPositionAt_of_exists_etaleChart ⟨U, hxU, m, ch, fun _ => none, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `r _hr s _hs t hrt _hst`. Simplify using `at hrt`. Introduce `r hr _hnone`. Establish `hr1 : r < 1` using `by simpa using hr`. Establish `hr0 : r = 0` using `by omega`.

Substitute `hr0` using the available equality. Conclude with `keyU`. Introduce `r _hr t hrt`. Simplify using `at hrt`. Establish `h2 : ((MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i)).comap (MaxContactOpenCover.coverPieceIso T hv i).inv = (MaxContactOpenCover.coverEtaleChart T hv i c).coordIdeal {j}`.

Rewrite using `[hres i, hlocal, MaxContactOpenCover.coverEtaleChart_coordIdeal]`. Establish `key` using `h1.trans h2`. Use `inStrictNormalCrossingPositionAt_of_exists_etaleChart ⟨MaxContactOpenCover.coverTripleOpen T hv i, hxi, n, MaxContactOpenCover.coverEtaleChart T hv i c, fun _ => some j, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `r hr s hs t _hrt _hst`. Establish `hr1 : r < 1` using `by simpa using hr`.

Establish `hs1 : s < 1` using `by simpa using hs`. Use linear arithmetic over natural numbers and integers. Introduce `r _hr hnone`. Simplify using `at hnone`. Introduce `r hr t hrt`.

Establish `hr1 : r < 1` using `by simpa using hr`. Establish `hr0 : r = 0` using `by omega`. Substitute `hr0` using the available equality. Take `rfl : j = t` from `Option.some.inj hrt`. Conclude with `key`.
-/
theorem inStrictNormalCrossingPositionAt_coverMaxContactIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
    (hres : ∀ i : (MaxContactCoverData.chosenCoverData T hv).idx,
      (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
        (MaxContactCoverData.chosenCoverData T hv).localIdeal i)
    (x : ↥(MaxContactCoverData.coverTriple T hv).scheme) :
    InStrictNormalCrossingPositionAt (MaxContactCoverData.coverTriple T hv).structMap
      [MaxContactCoverData.coverMaxContactIdeal T hv] x := by
  obtain ⟨i, hxi⟩ := MaxContactOpenCover.exists_mem_coverTripleOpen T hv x
  have h1 := MaxContactOpenCover.restrictIdeal_coverTripleOpen T hv i (MaxContactCoverData.coverMaxContactIdeal T hv)
  rcases hgood.dichotomy i with ⟨_hdisj, htop⟩ | ⟨n, c, j, hlocal, _hmc⟩
  · have h2 : ((MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i)).comap
        (MaxContactOpenCover.coverPieceIso T hv i).inv = ⊤ := by
      rw [hres i, htop]
      exact Scheme.IdealSheafData.comap_top _
    have key := h1.trans h2
    have hsm : AlgebraicGeometry.Smooth (MaxContactCoverData.coverTriple T hv).structMap := by
      have := MaxContactCoverData.smooth_coverMap_of_isAdmissible T hv
      have := hv.smooth
      exact (inferInstance : AlgebraicGeometry.Smooth
        (MaxContactCoverData.coverMap T hv ≫ T.structMap))
    obtain ⟨U, m, hxU, hUle, -, ⟨ch⟩⟩ :=
      exists_etaleChart_le (MaxContactCoverData.coverTriple T hv).structMap x
        (MaxContactOpenCover.coverTripleOpen T hv i) hxi
    have keyU : restrictIdeal (MaxContactCoverData.coverMaxContactIdeal T hv) U = ⊤ := by
      apply restrictIdeal_eq_top_of_le <;> assumption
    refine inStrictNormalCrossingPositionAt_of_exists_etaleChart ⟨U, hxU, m, ch, fun _ => none, ?_, ?_, ?_⟩
    · intro r _hr s _hs t hrt _hst
      simp at hrt
    · intro r hr _hnone
      have hr1 : r < 1 := by simpa using hr
      have hr0 : r = 0 := by omega
      subst hr0
      exact keyU
    · intro r _hr t hrt
      simp at hrt
  · have h2 : ((MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i)).comap
        (MaxContactOpenCover.coverPieceIso T hv i).inv = (MaxContactOpenCover.coverEtaleChart T hv i c).coordIdeal {j} := by
      rw [hres i, hlocal, MaxContactOpenCover.coverEtaleChart_coordIdeal]
    have key := h1.trans h2
    refine inStrictNormalCrossingPositionAt_of_exists_etaleChart
      ⟨MaxContactOpenCover.coverTripleOpen T hv i, hxi, n, MaxContactOpenCover.coverEtaleChart T hv i c, fun _ => some j,
        ?_, ?_, ?_⟩
    · intro r hr s hs t _hrt _hst
      have hr1 : r < 1 := by simpa using hr
      have hs1 : s < 1 := by simpa using hs
      omega
    · intro r _hr hnone
      simp at hnone
    · intro r hr t hrt
      have hr1 : r < 1 := by simpa using hr
      have hr0 : r = 0 := by omega
      subst hr0
      obtain rfl : j = t := Option.some.inj hrt
      exact key

/- English proof (translation)
Use `(inStrictNormalCrossingPosition_iff _ _).mpr ⟨?_, fun x => inStrictNormalCrossingPositionAt_coverMaxContactIdeal T hv hgood hres x⟩` and prove the remaining obligations. Introduce `D hD`. Establish `hD' : D = MaxContactCoverData.coverMaxContactIdeal T hv` using `List.mem_singleton.mp hD`. Substitute `hD'` using the available equality. Conclude with `hsm`.
-/
theorem inStrictNormalCrossingPosition_coverMaxContactIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
    (hres : ∀ i : (MaxContactCoverData.chosenCoverData T hv).idx,
      (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
        (MaxContactCoverData.chosenCoverData T hv).localIdeal i)
    (hsm : IsSmoothDivisor (MaxContactCoverData.coverTriple T hv).structMap
      (MaxContactCoverData.coverMaxContactIdeal T hv)) :
    InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple T hv).structMap
      [MaxContactCoverData.coverMaxContactIdeal T hv] := by
  refine (inStrictNormalCrossingPosition_iff _ _).mpr
    ⟨?_, fun x => inStrictNormalCrossingPositionAt_coverMaxContactIdeal T hv hgood hres x⟩
  intro D hD
  have hD' : D = MaxContactCoverData.coverMaxContactIdeal T hv := List.mem_singleton.mp hD
  subst hD'
  exact hsm

end FunctorialResolution.EmbeddedResolution

end
