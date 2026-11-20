import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactCoordinate
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FiniteKrullDim
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMapSurjective
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.KrullDimClosedSubset
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactOpenCover

/- English proof (translation)
The claim follows from `MorphismProperty.of_isPullback hsq.flip hg`.
-/
private theorem isOpenImmersion_fst_of_isPullback
    {P' X' Y' Z' : Scheme.{u}} {p₁ : P' ⟶ X'} {p₂ : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    (hsq : IsPullback p₁ p₂ f' g') (hg : IsOpenImmersion g') : IsOpenImmersion p₁ :=
  MorphismProperty.of_isPullback hsq.flip hg

/- English proof (translation)
Introduce `x`. Take `⟨U, hxU, hU⟩` from `hg (snd.base x)`. Conclude with `⟨_, hxU, isOpenImmersion_fst_of_isPullback ((isPullback_morphismRestrict snd U).flip.paste_horiz hsq) hU⟩`.
-/
theorem isLocalIsomorphism_fst_of_isPullback {P X Y Z : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hsq : IsPullback fst snd f g)
    (hg : MaxContactFunctoriality.IsLocalIsomorphism g) :
    MaxContactFunctoriality.IsLocalIsomorphism fst := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hg (snd.base x)
  exact ⟨_, hxU, isOpenImmersion_fst_of_isPullback
    ((isPullback_morphismRestrict snd U).flip.paste_horiz hsq) hU⟩

abbrev coverPiece (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) : Scheme.{u} :=
  (((MaxContactCoverData.chosenCoverData T hv).opens i : T.scheme.Opens) : Scheme.{u})

abbrev coverPieceι (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    coverPiece T hv i ⟶ (MaxContactCoverData.coverTriple T hv).scheme :=
  Sigma.ι (fun j : (MaxContactCoverData.chosenCoverData T hv).idx =>
    (((MaxContactCoverData.chosenCoverData T hv).opens j : T.scheme.Opens) : Scheme.{u})) i

/- English proof (translation)
Establish `h : IsOpenImmersion (Sigma.ι (fun j : (MaxContactCoverData.chosenCoverData T hv).idx => (((MaxContactCoverData.chosenCoverData T hv).opens j : T.scheme.Opens) : Scheme.{u})) i)` using `inferInstance`. Conclude with `h`.
-/
theorem isOpenImmersion_coverPieceι (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    IsOpenImmersion (coverPieceι T hv i) := by
  have h : IsOpenImmersion (Sigma.ι (fun j : (MaxContactCoverData.chosenCoverData T hv).idx =>
      (((MaxContactCoverData.chosenCoverData T hv).opens j : T.scheme.Opens) : Scheme.{u})) i) :=
    inferInstance
  exact h

instance instIsOpenImmersionStarι (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    IsOpenImmersion (coverPieceι T hv i) :=
  isOpenImmersion_coverPieceι T hv i

abbrev coverTripleOpen (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    (MaxContactCoverData.coverTriple T hv).scheme.Opens :=
  (coverPieceι T hv i).opensRange

abbrev coverTriplePiece (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) : Scheme.{u} :=
  ((coverTripleOpen T hv i : (MaxContactCoverData.coverTriple T hv).scheme.Opens) : Scheme.{u})

/- English proof (translation)
The claim follows from `((coverTripleOpen T hv i).range_ι).symm`.
-/
theorem range_coverPieceι (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    Set.range (coverPieceι T hv i).base = Set.range (coverTripleOpen T hv i).ι.base :=
  ((coverTripleOpen T hv i).range_ι).symm

def coverPieceIso (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    coverPiece T hv i ≅ coverTriplePiece T hv i :=
  IsOpenImmersion.isoOfRangeEq (coverPieceι T hv i) (coverTripleOpen T hv i).ι (range_coverPieceι T hv i)

/- English proof (translation)
Take `⟨⟨i, y⟩, hy⟩` from `(AlgebraicGeometry.sigmaMk (fun j : (MaxContactCoverData.chosenCoverData T hv).idx => (((MaxContactCoverData.chosenCoverData T hv).opens j : T.scheme.Opens) : Scheme.{u}))).surjective x`. Use `⟨i, ?_⟩` and prove the remaining obligations. Use `show x ∈ Set.range (Sigma.ι (fun j : (MaxContactCoverData.chosenCoverData T hv).idx => (((MaxContactCoverData.chosenCoverData T hv).opens j : T.scheme.Opens) : Scheme.{u})) i).base`. Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy]`.

Simplify using the standard rewrite rules.
-/
theorem exists_mem_coverTripleOpen (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (x : ↥(MaxContactCoverData.coverTriple T hv).scheme) :
    ∃ i : (MaxContactCoverData.chosenCoverData T hv).idx, x ∈ coverTripleOpen T hv i := by
  obtain ⟨⟨i, y⟩, hy⟩ := (AlgebraicGeometry.sigmaMk
    (fun j : (MaxContactCoverData.chosenCoverData T hv).idx =>
      (((MaxContactCoverData.chosenCoverData T hv).opens j : T.scheme.Opens) : Scheme.{u}))).surjective x
  refine ⟨i, ?_⟩
  show x ∈ Set.range (Sigma.ι (fun j : (MaxContactCoverData.chosenCoverData T hv).idx =>
    (((MaxContactCoverData.chosenCoverData T hv).opens j : T.scheme.Opens) : Scheme.{u})) i).base
  refine ⟨y, ?_⟩
  rw [← hy]
  simp

/- English proof (translation)
Apply `AlgebraicGeometry.IsOpenImmersion.lift_fac` to reduce the goal to its premises.
-/
private theorem coverPieceIso_inv_comp_coverPieceι (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    (coverPieceIso T hv i).inv ≫ coverPieceι T hv i = (coverTripleOpen T hv i).ι := by
  apply AlgebraicGeometry.IsOpenImmersion.lift_fac

/- English proof (translation)
Rewrite using `[MaxContactCoverData.coverMap_eq_sigmaOpensDesc]`. Conclude with `sigma_ι_sigmaOpensDesc T.scheme (MaxContactCoverData.chosenCoverData T hv).opens i`.
-/
private theorem coverPieceι_comp_coverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    coverPieceι T hv i ≫ MaxContactCoverData.coverMap T hv =
      ((MaxContactCoverData.chosenCoverData T hv).opens i).ι := by
  rw [MaxContactCoverData.coverMap_eq_sigmaOpensDesc]
  exact sigma_ι_sigmaOpensDesc T.scheme (MaxContactCoverData.chosenCoverData T hv).opens i

/- English proof (translation)
Establish `h` using `coverPieceIso_inv_comp_coverPieceι T hv i`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[coverPieceι_comp_coverMap T hv i]`.
-/
theorem coverTripleOpen_ι_comp_coverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    (coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv =
      (coverPieceIso T hv i).inv ≫ ((MaxContactCoverData.chosenCoverData T hv).opens i).ι := by
  have h := coverPieceIso_inv_comp_coverPieceι T hv i
  calc (coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv
      = ((coverPieceIso T hv i).inv ≫ coverPieceι T hv i) ≫ MaxContactCoverData.coverMap T hv := by rw [h]
    _ = (coverPieceIso T hv i).inv ≫ (coverPieceι T hv i ≫ MaxContactCoverData.coverMap T hv) :=
        Category.assoc _ _ _
    _ = (coverPieceIso T hv i).inv ≫ ((MaxContactCoverData.chosenCoverData T hv).opens i).ι := by
        rw [coverPieceι_comp_coverMap T hv i]

/- English proof (translation)
Simplify using `only [restrictIdeal_eq_comap_ι, ← coverPieceIso_inv_comp_coverPieceι T hv i, Scheme.IdealSheafData.comap_comp]`.
-/
theorem restrictIdeal_coverTripleOpen (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx)
    (J : (MaxContactCoverData.coverTriple T hv).scheme.IdealSheafData) :
    restrictIdeal J (coverTripleOpen T hv i) = (J.comap (coverPieceι T hv i)).comap (coverPieceIso T hv i).inv := by
  simp only [restrictIdeal_eq_comap_ι, ← coverPieceIso_inv_comp_coverPieceι T hv i,
    Scheme.IdealSheafData.comap_comp]

/- English proof (translation)
Introduce `x`. Take `⟨i, hxi⟩` from `exists_mem_coverTripleOpen T hv x`. Establish `hψ : IsOpenImmersion ((coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv)`. Rewrite using `[coverTripleOpen_ι_comp_coverMap T hv i]`. Use `infer_instance`.

Conclude with `⟨coverTripleOpen T hv i, hxi, hψ⟩`.
-/
theorem isLocalIsomorphism_coverMap (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    MaxContactFunctoriality.IsLocalIsomorphism (MaxContactCoverData.coverMap T hv) := by
  intro x
  obtain ⟨i, hxi⟩ := exists_mem_coverTripleOpen T hv x
  have hψ : IsOpenImmersion ((coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv) := by
    rw [coverTripleOpen_ι_comp_coverMap T hv i]
    infer_instance
  exact ⟨coverTripleOpen T hv i, hxi, hψ⟩

/- English proof (translation)
Establish `h1 : c.map ≫ affineSpaceFinToSpec T.base n = ((MaxContactCoverData.chosenCoverData T hv).opens i).ι ≫ T.structMap` using `c.comp_struct`. Establish `h2` using `coverTripleOpen_ι_comp_coverMap T hv i`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1]`. Use `_ = ((coverPieceIso T hv i).inv ≫ ((MaxContactCoverData.chosenCoverData T hv).opens i).ι) ≫ T.structMap := (Category.assoc _ _ _).symm`.

Use `_ = ((coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv) ≫ T.structMap := by rw [h2]`. Use `_ = (coverTripleOpen T hv i).ι ≫ (MaxContactCoverData.coverMap T hv ≫ T.structMap) := Category.assoc _ _ _`.
-/
private theorem coverPieceIso_inv_comp_map_comp_affineSpaceFinToSpec (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) {n : ℕ}
    (c : EtaleChart T.structMap ((MaxContactCoverData.chosenCoverData T hv).opens i) n) :
    ((coverPieceIso T hv i).inv ≫ c.map) ≫ affineSpaceFinToSpec T.base n =
      (coverTripleOpen T hv i).ι ≫ (MaxContactCoverData.coverMap T hv ≫ T.structMap) := by
  have h1 : c.map ≫ affineSpaceFinToSpec T.base n =
      ((MaxContactCoverData.chosenCoverData T hv).opens i).ι ≫ T.structMap := c.comp_struct
  have h2 := coverTripleOpen_ι_comp_coverMap T hv i
  calc ((coverPieceIso T hv i).inv ≫ c.map) ≫ affineSpaceFinToSpec T.base n
      = (coverPieceIso T hv i).inv ≫ (c.map ≫ affineSpaceFinToSpec T.base n) := Category.assoc _ _ _
    _ = (coverPieceIso T hv i).inv ≫ (((MaxContactCoverData.chosenCoverData T hv).opens i).ι ≫ T.structMap) := by
        rw [h1]
    _ = ((coverPieceIso T hv i).inv ≫ ((MaxContactCoverData.chosenCoverData T hv).opens i).ι) ≫ T.structMap :=
        (Category.assoc _ _ _).symm
    _ = ((coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv) ≫ T.structMap := by rw [h2]
    _ = (coverTripleOpen T hv i).ι ≫ (MaxContactCoverData.coverMap T hv ≫ T.structMap) :=
        Category.assoc _ _ _

/- English proof (translation)
Establish `: AlgebraicGeometry.Etale c.map` using `c.isEtale`. Establish `: IsIso (coverPieceIso T hv i).inv` using `inferInstance`. Establish `: IsOpenImmersion (coverPieceIso T hv i).inv` using `inferInstance`. Establish `: AlgebraicGeometry.Etale (coverPieceIso T hv i).inv` using `inferInstance`. Use `infer_instance`.
-/
private theorem etale_coverPieceIso_inv_comp_map (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) {n : ℕ}
    (c : EtaleChart T.structMap ((MaxContactCoverData.chosenCoverData T hv).opens i) n) :
    AlgebraicGeometry.Etale ((coverPieceIso T hv i).inv ≫ c.map) := by
  have : AlgebraicGeometry.Etale c.map := c.isEtale
  have : IsIso (coverPieceIso T hv i).inv := inferInstance
  have : IsOpenImmersion (coverPieceIso T hv i).inv := inferInstance
  have : AlgebraicGeometry.Etale (coverPieceIso T hv i).inv := inferInstance
  infer_instance

def coverEtaleChart (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) {n : ℕ}
    (c : EtaleChart T.structMap ((MaxContactCoverData.chosenCoverData T hv).opens i) n) :
    EtaleChart (MaxContactCoverData.coverMap T hv ≫ T.structMap) (coverTripleOpen T hv i) n where
  map := (coverPieceIso T hv i).inv ≫ c.map
  comp_struct := coverPieceIso_inv_comp_map_comp_affineSpaceFinToSpec T hv i c
  isEtale := etale_coverPieceIso_inv_comp_map T hv i c

/- English proof (translation)
Establish `key : (coordSubspaceIdeal T.base n S).comap ((coverPieceIso T hv i).inv ≫ c.map) = ((coordSubspaceIdeal T.base n S).comap c.map).comap (coverPieceIso T hv i).inv`. Rewrite using `[Scheme.IdealSheafData.comap_comp]`. Establish `h1 : (coverEtaleChart T hv i c).coordIdeal S = (coordSubspaceIdeal T.base n S).comap ((coverPieceIso T hv i).inv ≫ c.map)` using `EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal (coverEtaleChart T hv i c) S`. Establish `h2 : (c.coordIdeal S).comap (coverPieceIso T hv i).inv = ((coordSubspaceIdeal T.base n S).comap c.map).comap (coverPieceIso T hv i).inv` using `congrArg (fun J => J.comap (coverPieceIso T hv i).inv) (EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal c S)`. Conclude with `h1.trans (key.trans h2.symm)`.
-/
theorem coverEtaleChart_coordIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) {n : ℕ}
    (c : EtaleChart T.structMap ((MaxContactCoverData.chosenCoverData T hv).opens i) n)
    (S : Finset (Fin n)) :
    (coverEtaleChart T hv i c).coordIdeal S = (c.coordIdeal S).comap (coverPieceIso T hv i).inv := by
  have key : (coordSubspaceIdeal T.base n S).comap ((coverPieceIso T hv i).inv ≫ c.map)
      = ((coordSubspaceIdeal T.base n S).comap c.map).comap (coverPieceIso T hv i).inv := by
    rw [Scheme.IdealSheafData.comap_comp]
  have h1 : (coverEtaleChart T hv i c).coordIdeal S
      = (coordSubspaceIdeal T.base n S).comap ((coverPieceIso T hv i).inv ≫ c.map) :=
    EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal (coverEtaleChart T hv i c) S
  have h2 : (c.coordIdeal S).comap (coverPieceIso T hv i).inv
      = ((coordSubspaceIdeal T.base n S).comap c.map).comap (coverPieceIso T hv i).inv :=
    congrArg (fun J => J.comap (coverPieceIso T hv i).inv) (EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal c S)
  exact h1.trans (key.trans h2.symm)

/- English proof (translation)
Use `hf` as an intermediate fact. Conclude with `QuasiCompact.compactSpace_of_compactSpace f`.
-/
private theorem compactSpace_of_quasiCompact_toSpec {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) (hf : AlgebraicGeometry.QuasiCompact f) : CompactSpace ↥X := by
  have := hf
  exact QuasiCompact.compactSpace_of_compactSpace f

/- English proof (translation)
Use `hv.charZero` as an intermediate fact. Use `hv.smooth` as an intermediate fact. Establish `hm : 1 ≤ MaxContactCoverData.tunedMult T` using `one_le_tuningExponent T.mult`. Distinguish the cases in `hx : x ∈ orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)`. Establish `hord : orderAt (MaxContactCoverData.balancedTunedIdeal T hv) x = ((MaxContactCoverData.tunedMult T : ℕ) : ℕ∞)` using `le_antisymm (h x) ((mem_orderAtLeastLocus_iff _ _ _).1 hx)`.

Take `⟨V, hVaff, hxV, n, c, j, hmc, -⟩` from `exists_isMaxContactCoord T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv) hm x hord`. Conclude with `⟨V, c.coordIdeal {j}, hxV, hVaff, Or.inr ⟨n, c, j, rfl, hmc⟩⟩`. Establish `hcl : IsClosed (orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))` using `isClosed_orderAtLeastLocus T.base T.structMap _ _`. Take `⟨V, n, hxV, hVW, hVaff, -⟩` from `exists_etaleChart_le T.structMap x ⟨(orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))ᶜ, hcl.isOpen_compl⟩ hx`. Use `⟨V, ⊤, hxV, hVaff, Or.inl ⟨?_, rfl⟩⟩` and prove the remaining obligations.

Use `Set.disjoint_left.2 ?_` and prove the remaining obligations. Introduce `y hyS hyV`. Conclude with `(hVW hyV) hyS`.
-/
private theorem exists_affineOpen_maxContactCoord_or_disjoint_locus (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    (h : ∀ x : ↥T.scheme,
      orderAt (MaxContactCoverData.balancedTunedIdeal T hv) x ≤ ((MaxContactCoverData.tunedMult T : ℕ) : ℕ∞))
    (x : ↥T.scheme) :
    ∃ (V : T.scheme.Opens) (J : (V : Scheme.{u}).IdealSheafData),
      x ∈ V ∧ AlgebraicGeometry.IsAffineOpen V ∧
        ((Disjoint (orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
              (V : Set ↥T.scheme) ∧ J = ⊤) ∨
          ∃ (n : ℕ) (c : EtaleChart T.structMap V n) (j : Fin n),
            J = c.coordIdeal {j} ∧
              MaxContactReduction.IsMaxContactCoord T.base T.structMap
                (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) c j) := by
  classical
  have := hv.charZero
  have := hv.smooth
  have hm : 1 ≤ MaxContactCoverData.tunedMult T := one_le_tuningExponent T.mult
  by_cases hx : x ∈ orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)
  · have hord : orderAt (MaxContactCoverData.balancedTunedIdeal T hv) x
        = ((MaxContactCoverData.tunedMult T : ℕ) : ℕ∞) :=
      le_antisymm (h x) ((mem_orderAtLeastLocus_iff _ _ _).1 hx)
    obtain ⟨V, hVaff, hxV, n, c, j, hmc, -⟩ :=
      exists_isMaxContactCoord T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv) hm x hord
    exact ⟨V, c.coordIdeal {j}, hxV, hVaff, Or.inr ⟨n, c, j, rfl, hmc⟩⟩
  · have hcl : IsClosed
        (orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)) :=
      isClosed_orderAtLeastLocus T.base T.structMap _ _
    obtain ⟨V, n, hxV, hVW, hVaff, -⟩ :=
      exists_etaleChart_le T.structMap x
        ⟨(orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))ᶜ,
          hcl.isOpen_compl⟩ hx
    refine ⟨V, ⊤, hxV, hVaff, Or.inl ⟨?_, rfl⟩⟩
    refine Set.disjoint_left.2 ?_
    intro y hyS hyV
    exact (hVW hyV) hyS

/- English proof (translation)
Use `hv.locallyOfFiniteType` as an intermediate fact. Establish `: CompactSpace ↥T.scheme` using `compactSpace_of_quasiCompact_toSpec T.structMap hv.quasiCompact`. Use `choose V J hxV hVaff hdich using exists_affineOpen_maxContactCoord_or_disjoint_locus T hv h`. Establish `hcover : (Set.univ : Set ↥T.scheme) ⊆ ⋃ x : ↥T.scheme, ((V x : T.scheme.Opens) : Set ↥T.scheme)`. Introduce `y _`.

Conclude with `Set.mem_iUnion.2 ⟨y, hxV y⟩`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun x : ↥T.scheme => ((V x : T.scheme.Opens) : Set ↥T.scheme)) (fun x => (V x).isOpen) hcover`. Use `⟨{ idx := {y : ↥T.scheme // y ∈ t}, finiteIdx := inferInstance, opens := fun i => V i.1, localIdeal := fun i => J i.1 }, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `le_antisymm le_top ?_` and prove the remaining obligations. Introduce `y _`.

Take `⟨i, hi, hyi⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ y))`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hyi⟩`. Conclude with `fun i => hVaff i.1`. Conclude with `fun i => hdich i.1`.
-/
theorem exists_isMaxContactCover (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (h : ∀ x : ↥T.scheme,
      orderAt (MaxContactCoverData.balancedTunedIdeal T hv) x ≤ ((MaxContactCoverData.tunedMult T : ℕ) : ℕ∞)) :
    ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T,
      MaxContactReduction.IsMaxContactCover T D hv.locallyOfFiniteType (MaxContactCoverData.balancedTunedIdeal T hv)
        (MaxContactCoverData.tunedMult T) := by
  classical
  have := hv.locallyOfFiniteType
  have : CompactSpace ↥T.scheme := compactSpace_of_quasiCompact_toSpec T.structMap hv.quasiCompact
  choose V J hxV hVaff hdich using exists_affineOpen_maxContactCoord_or_disjoint_locus T hv h
  have hcover : (Set.univ : Set ↥T.scheme) ⊆
      ⋃ x : ↥T.scheme, ((V x : T.scheme.Opens) : Set ↥T.scheme) := by
    intro y _
    exact Set.mem_iUnion.2 ⟨y, hxV y⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : ↥T.scheme => ((V x : T.scheme.Opens) : Set ↥T.scheme))
    (fun x => (V x).isOpen) hcover
  refine ⟨{ idx := {y : ↥T.scheme // y ∈ t},
            finiteIdx := inferInstance,
            opens := fun i => V i.1,
            localIdeal := fun i => J i.1 }, ?_, ?_, ?_⟩
  · refine le_antisymm le_top ?_
    intro y _
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hyi⟩
  · exact fun i => hVaff i.1
  · exact fun i => hdich i.1

def tunedTriple (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) : MarkedIdealWithBoundary.{u} where
  base := T.base
  scheme := T.scheme
  structMap := T.structMap
  ideal := MaxContactCoverData.balancedTunedIdeal T hv
  mult := MaxContactCoverData.tunedMult T
  boundary := T.boundary

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem tunedTriple_baseField (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (tunedTriple T hv).base = T.base := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem tunedTriple_scheme (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (tunedTriple T hv).scheme = T.scheme := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem tunedTriple_structureMorphism (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (tunedTriple T hv).structMap = T.structMap := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem tunedTriple_ideal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (tunedTriple T hv).ideal = MaxContactCoverData.balancedTunedIdeal T hv := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem tunedTriple_mult (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (tunedTriple T hv).mult = MaxContactCoverData.tunedMult T := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem tunedTriple_boundary (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    (tunedTriple T hv).boundary = T.boundary := rfl

/- English proof (translation)
The claim follows from `{ charZero := hv.charZero locallyOfFiniteType := hv.locallyOfFiniteType nonzeroOnComponents := hnz one_le_mult := one_le_tuningExponent T.mult quasiCompact := hv.quasiCompact smooth := hv.smooth snc := hv.snc }`.
-/
theorem isAdmissible_tunedTriple (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hnz : NonzeroOnComponents (MaxContactCoverData.balancedTunedIdeal T hv)) :
    (tunedTriple T hv).IsAdmissible :=
  { charZero := hv.charZero
    locallyOfFiniteType := hv.locallyOfFiniteType
    nonzeroOnComponents := hnz
    one_le_mult := one_le_tuningExponent T.mult
    quasiCompact := hv.quasiCompact
    smooth := hv.smooth
    snc := hv.snc }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coverTriple_eq_tunedTriple_pullbackAlong (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    MaxContactCoverData.coverTriple T hv =
      (tunedTriple T hv).pullbackAlong (MaxContactCoverData.chosenCoverData T hv).disjointUnion
        (MaxContactCoverData.coverMap T hv ≫ T.structMap) (MaxContactCoverData.coverMap T hv) :=
  rfl

/- English proof (translation)
The claim follows from `isAffine_sigmaOpens T.scheme (MaxContactCoverData.chosenCoverData T hv).opens hgood.isAffine`.
-/
theorem isAffine_coverTriple_scheme (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)) :
    AlgebraicGeometry.IsAffine (MaxContactCoverData.coverTriple T hv).scheme :=
  isAffine_sigmaOpens T.scheme (MaxContactCoverData.chosenCoverData T hv).opens hgood.isAffine

/- English proof (translation)
Establish `: AlgebraicGeometry.IsAffine ((MaxContactCoverData.chosenCoverData T hv).disjointUnion)` using `isAffine_coverTriple_scheme T hv hgood`. Establish `: AlgebraicGeometry.IsAffine (MaxContactCoverData.coverTriple T hv).scheme` using `isAffine_coverTriple_scheme T hv hgood`. Establish `: Subsingleton ↥(AlgebraicGeometry.Spec (CommRingCat.of T.base))` using `inferInstance`. Prove the components needed by the constructor for the conclusion. Introduce `U _hU _hUc`.

Distinguish the cases in `hUe : U = ∅`. Substitute `hUe` using the available equality. Rewrite using `[Set.preimage_empty]`. Conclude with `isCompact_empty`. Establish `hUu : U = Set.univ`.

Take `⟨u, hu⟩` from `Set.nonempty_iff_ne_empty.mpr hUe`. Use `Set.eq_univ_of_forall fun z => ?_` and prove the remaining obligations. Rewrite using `[Subsingleton.elim z u]` and apply the resulting hypothesis. Substitute `hUu` using the available equality. Rewrite using `[Set.preimage_univ]`.

Conclude with `isCompact_univ`.
-/
theorem quasiCompact_coverMap_comp_structureMorphism (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)) :
    AlgebraicGeometry.QuasiCompact (MaxContactCoverData.coverMap T hv ≫ T.structMap) := by
  have : AlgebraicGeometry.IsAffine ((MaxContactCoverData.chosenCoverData T hv).disjointUnion) :=
    isAffine_coverTriple_scheme T hv hgood
  have : AlgebraicGeometry.IsAffine (MaxContactCoverData.coverTriple T hv).scheme :=
    isAffine_coverTriple_scheme T hv hgood
  have : Subsingleton ↥(AlgebraicGeometry.Spec (CommRingCat.of T.base)) := inferInstance
  constructor
  intro U _hU _hUc
  by_cases hUe : U = ∅
  · subst hUe
    rw [Set.preimage_empty]
    exact isCompact_empty
  · have hUu : U = Set.univ := by
      obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.mpr hUe
      refine Set.eq_univ_of_forall fun z => ?_
      rwa [Subsingleton.elim z u]
    subst hUu
    rw [Set.preimage_univ]
    exact isCompact_univ

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun Z => h.elim Z.2.1.choose⟩`.
-/
private theorem isEmpty_irreducibleCloseds_of_isEmpty {C : Type u} [TopologicalSpace C] (h : IsEmpty C) :
    IsEmpty (TopologicalSpace.IrreducibleCloseds C) :=
  ⟨fun Z => h.elim Z.2.1.choose⟩

/- English proof (translation)
Use `isEmpty_irreducibleCloseds_of_isEmpty h` as an intermediate fact. Use `show Order.krullDim (TopologicalSpace.IrreducibleCloseds C) ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds B)`. Conclude with `Order.krullDim_le_of_strictMono (fun Z : TopologicalSpace.IrreducibleCloseds C => isEmptyElim Z) (fun a _ _ => isEmptyElim a)`.
-/
private theorem topologicalKrullDim_le_of_isEmpty {C B : Type u} [TopologicalSpace C]
    [TopologicalSpace B] (h : IsEmpty C) :
    topologicalKrullDim C ≤ topologicalKrullDim B := by
  have := isEmpty_irreducibleCloseds_of_isEmpty h
  show Order.krullDim (TopologicalSpace.IrreducibleCloseds C)
      ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds B)
  exact Order.krullDim_le_of_strictMono
    (fun Z : TopologicalSpace.IrreducibleCloseds C => isEmptyElim Z)
    (fun a _ _ => isEmptyElim a)

/- English proof (translation)
Introduce `hb`. Establish `hb' : Order.krullDim (TopologicalSpace.IrreducibleCloseds B) = ⊥` using `hb`. Establish `hE : IsEmpty (TopologicalSpace.IrreducibleCloseds B)` using `Order.krullDim_eq_bot_iff.mp hb'`. Conclude with `hE.elim ⟨closure {b}, isIrreducible_singleton.closure, isClosed_closure⟩`.
-/
private theorem topologicalKrullDim_ne_bot {B : Type u} [TopologicalSpace B] (b : B) :
    topologicalKrullDim B ≠ ⊥ := by
  intro hb
  have hb' : Order.krullDim (TopologicalSpace.IrreducibleCloseds B) = ⊥ := hb
  have hE : IsEmpty (TopologicalSpace.IrreducibleCloseds B) := Order.krullDim_eq_bot_iff.mp hb'
  exact hE.elim ⟨closure {b}, isIrreducible_singleton.closure, isClosed_closure⟩

/- English proof (translation)
Use `h` as an intermediate fact. Conclude with `f.isOpenEmbedding.isInducing.topologicalKrullDim_le`.
-/
private theorem topologicalKrullDim_le_of_isOpenImmersion {P Q : Scheme.{u}} (f : P ⟶ Q)
    (h : IsOpenImmersion f) : topologicalKrullDim ↥P ≤ topologicalKrullDim ↥Q := by
  have := h
  exact f.isOpenEmbedding.isInducing.topologicalKrullDim_le

/- English proof (translation)
Establish `hψ : IsOpenImmersion ((coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv)`. Rewrite using `[coverTripleOpen_ι_comp_coverMap T hv i]`. Use `infer_instance`. Conclude with `topologicalKrullDim_le_of_isOpenImmersion ((coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv) hψ`.
-/
private theorem topologicalKrullDim_coverTripleOpen_le (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    topologicalKrullDim
        ↥(↑(coverTripleOpen T hv i) : Set ↥(MaxContactCoverData.coverTriple T hv).scheme)
      ≤ topologicalKrullDim ↥T.scheme := by
  have hψ : IsOpenImmersion ((coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv) := by
    rw [coverTripleOpen_ι_comp_coverMap T hv i]
    infer_instance
  exact topologicalKrullDim_le_of_isOpenImmersion
    ((coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv) hψ

/- English proof (translation)
Establish `hd : topologicalKrullDim ↥T.scheme < ⊤` using `hv.topologicalKrullDim_lt_top`. Distinguish the cases in `hTe : IsEmpty ↥T.scheme`. Establish `hce : IsEmpty ↥(MaxContactCoverData.coverTriple T hv).scheme` using `⟨fun x => hTe.elim ((MaxContactCoverData.coverMap T hv).base x)⟩`. Conclude with `krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le _ _ (topologicalKrullDim_le_of_isEmpty hce) hd`. Take `⟨y⟩ : Nonempty ↥T.scheme` from `not_isEmpty_iff.mp hTe`.

Establish `hbot : topologicalKrullDim ↥T.scheme ≠ ⊥` using `topologicalKrullDim_ne_bot y`. Take `⟨m, hm⟩` from `WithBot.ne_bot_iff_exists.mp hbot`. Establish `hmtop : m ≠ ⊤`. Introduce and unpack `rfl`. Rewrite `hm` using `[WithBot.coe_top]`.

Rewrite `hd` using `[← hm]`. Conclude with `lt_irrefl _ hd`. Take `⟨k, hk⟩` from `ENat.ne_top_iff_exists.mp hmtop`. Establish `hdeq : topologicalKrullDim ↥T.scheme = ((k : ℕ) : WithBot ℕ∞)`. Rewrite using `[← hm, ← hk]`.

Use `norm_cast`. Use `krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le _ _ ?_ hd` and prove the remaining obligations. Rewrite using `[hdeq]`. Use `topologicalKrullDim_le_natCast_of_isOpenCover (fun i : (MaxContactCoverData.chosenCoverData T hv).idx => (↑(coverTripleOpen T hv i) : Set ↥(MaxContactCoverData.coverTriple T hv).scheme)) (fun i => (coverTripleOpen T hv i).isOpen) ?_ k ?_` and prove the remaining obligations. Use `Set.eq_univ_of_forall fun x => ?_` and prove the remaining obligations.

Take `⟨i, hi⟩` from `exists_mem_coverTripleOpen T hv x`. Conclude with `Set.mem_iUnion.mpr ⟨i, hi⟩`. Introduce `i`. Establish `hpiece` using `topologicalKrullDim_coverTripleOpen_le T hv i`. Rewrite `hpiece` using `[hdeq]`.

Conclude with `hpiece`.
-/
theorem krullDimSucc_coverTriple_scheme_le_dim (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    krullDimSucc (MaxContactCoverData.coverTriple T hv).scheme ≤ T.krullDimSucc := by
  have hd : topologicalKrullDim ↥T.scheme < ⊤ := hv.topologicalKrullDim_lt_top
  by_cases hTe : IsEmpty ↥T.scheme
  · have hce : IsEmpty ↥(MaxContactCoverData.coverTriple T hv).scheme :=
      ⟨fun x => hTe.elim ((MaxContactCoverData.coverMap T hv).base x)⟩
    exact krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le _ _
      (topologicalKrullDim_le_of_isEmpty hce) hd
  · obtain ⟨y⟩ : Nonempty ↥T.scheme := not_isEmpty_iff.mp hTe
    have hbot : topologicalKrullDim ↥T.scheme ≠ ⊥ := topologicalKrullDim_ne_bot y
    obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hbot
    have hmtop : m ≠ ⊤ := by
      rintro rfl
      rw [WithBot.coe_top] at hm
      rw [← hm] at hd
      exact lt_irrefl _ hd
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hmtop
    have hdeq : topologicalKrullDim ↥T.scheme = ((k : ℕ) : WithBot ℕ∞) := by
      rw [← hm, ← hk]
      norm_cast
    refine krullDimSucc_le_krullDimSucc_of_topologicalKrullDim_le _ _ ?_ hd
    rw [hdeq]
    refine topologicalKrullDim_le_natCast_of_isOpenCover
      (fun i : (MaxContactCoverData.chosenCoverData T hv).idx =>
        (↑(coverTripleOpen T hv i) : Set ↥(MaxContactCoverData.coverTriple T hv).scheme))
      (fun i => (coverTripleOpen T hv i).isOpen) ?_ k ?_
    · refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨i, hi⟩ := exists_mem_coverTripleOpen T hv x
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    · intro i
      have hpiece := topologicalKrullDim_coverTripleOpen_le T hv i
      rw [hdeq] at hpiece
      exact hpiece

end MaxContactOpenCover

end FunctorialResolution.EmbeddedResolution

end
