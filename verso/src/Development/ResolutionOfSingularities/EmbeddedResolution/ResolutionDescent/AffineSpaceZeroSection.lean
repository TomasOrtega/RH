import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimensionPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceOrigin
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceProduct
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceChartPresentation
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceLinearEmbeddings
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.IntersectionComponentsFlatBaseChange
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IrreducibleComponentsFlatPreimage
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SupportFlatPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DetachedLocus
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Substitute `hI` using the available equality. Conclude with `⟨asIso i.toImage, i.toImage_imageι⟩`.
-/
private theorem exists_iso_subscheme_of_ker_eq {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (I : X.IdealSheafData) (hI : Scheme.Hom.ker i = I) :
    ∃ e : Z ≅ I.subscheme, e.hom ≫ I.subschemeι = i := by
  subst hI
  exact ⟨asIso i.toImage, i.toImage_imageι⟩

/- English proof (translation)
Take `⟨e, he⟩` from `exists_iso_subscheme_of_ker_eq i (Scheme.Hom.ker i) rfl`. Take `⟨e', he'⟩` from `exists_iso_subscheme_of_ker_eq i' ((Scheme.Hom.ker i).comap g) h`. Establish `h1 : IsPullback e'.hom i' ((Scheme.Hom.ker i).comap g).subschemeι (𝟙 X')` using `IsPullback.of_horiz_isIso ⟨by rw [he', Category.comp_id]⟩`. Establish `h2` using `isPullback_comapSubschemeHom (Scheme.Hom.ker i) g`. Establish `h3 : IsPullback e.inv (Scheme.Hom.ker i).subschemeι i (𝟙 X)` using `IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, Iso.inv_comp_eq]; exact he.symm⟩`.

Use `⟨(e'.hom ≫ comapSubschemeHom (Scheme.Hom.ker i) g) ≫ e.inv, ?_⟩` and prove the remaining obligations. Establish `h4` using `(h1.paste_horiz h2).paste_horiz h3`. Rewrite `h4` using `[Category.id_comp, Category.comp_id]`. Then use the resulting hypothesis.
-/
theorem exists_isPullback_of_ker_eq_comap {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (i' : Z' ⟶ X') [IsClosedImmersion i'] (g : X' ⟶ X)
    (h : Scheme.Hom.ker i' = (Scheme.Hom.ker i).comap g) :
    ∃ c : Z' ⟶ Z, IsPullback c i' i g := by
  obtain ⟨e, he⟩ := exists_iso_subscheme_of_ker_eq i (Scheme.Hom.ker i) rfl
  obtain ⟨e', he'⟩ := exists_iso_subscheme_of_ker_eq i' ((Scheme.Hom.ker i).comap g) h
  have h1 : IsPullback e'.hom i' ((Scheme.Hom.ker i).comap g).subschemeι (𝟙 X') :=
    IsPullback.of_horiz_isIso ⟨by rw [he', Category.comp_id]⟩
  have h2 := isPullback_comapSubschemeHom (Scheme.Hom.ker i) g
  have h3 : IsPullback e.inv (Scheme.Hom.ker i).subschemeι i (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, Iso.inv_comp_eq]; exact he.symm⟩
  refine ⟨(e'.hom ≫ comapSubschemeHom (Scheme.Hom.ker i) g) ≫ e.inv, ?_⟩
  have h4 := (h1.paste_horiz h2).paste_horiz h3
  rwa [Category.id_comp, Category.comp_id] at h4

abbrev opensPreimageProjLeft (k : Type u) [Field k] (M p : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).Opens) :
    (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin p))).Opens :=
  (Opens.map (projLeft k M p).base).obj U

/- English proof (translation)
Establish `hcomp : (U.ι ≫ affineSpaceInl k M p) ≫ projLeft k M p = U.ι`. Rewrite using `[Category.assoc, affineSpaceInl_comp_projLeft, Category.comp_id]`. Rewrite using `[Set.range_subset_iff]`. Introduce `x`. Establish `hx : (projLeft k M p) ((U.ι ≫ affineSpaceInl k M p) x) = U.ι x` using `congrArg (fun f : (U : Scheme.{u}) ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) => ⇑f x) hcomp`.

Establish `hmem : (U.ι ≫ affineSpaceInl k M p) x ∈ opensPreimageProjLeft k M p U` using `by show (projLeft k M p) ((U.ι ≫ affineSpaceInl k M p) x) ∈ U`. Rewrite using `[hx]`. Conclude with `x.2`. Conclude with `⟨⟨(U.ι ≫ affineSpaceInl k M p) x, hmem⟩, rfl⟩`.
-/
theorem range_affineSpaceInl_subset_range_opensPreimageProjLeft (k : Type u) [Field k] (M p : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).Opens) :
    Set.range ⇑(U.ι ≫ affineSpaceInl k M p) ⊆ Set.range ⇑(opensPreimageProjLeft k M p U).ι := by
  have hcomp : (U.ι ≫ affineSpaceInl k M p) ≫ projLeft k M p = U.ι := by
    rw [Category.assoc, affineSpaceInl_comp_projLeft, Category.comp_id]
  rw [Set.range_subset_iff]
  intro x
  have hx : (projLeft k M p) ((U.ι ≫ affineSpaceInl k M p) x) = U.ι x :=
    congrArg (fun f : (U : Scheme.{u}) ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) => ⇑f x) hcomp
  have hmem : (U.ι ≫ affineSpaceInl k M p) x ∈ opensPreimageProjLeft k M p U := by
    show (projLeft k M p) ((U.ι ≫ affineSpaceInl k M p) x) ∈ U
    rw [hx]
    exact x.2
  exact ⟨⟨(U.ι ≫ affineSpaceInl k M p) x, hmem⟩, rfl⟩

/- English proof (translation)
Establish `hfac : IsOpenImmersion.lift (opensPreimageProjLeft k M p U).ι (U.ι ≫ affineSpaceInl k M p) (range_affineSpaceInl_subset_range_opensPreimageProjLeft k M p U) ≫ (projLeft k M p ⁻¹ᵁ U).ι = U.ι ≫ affineSpaceInl k M p` using `IsOpenImmersion.lift_fac (opensPreimageProjLeft k M p U).ι (U.ι ≫ affineSpaceInl k M p) (range_affineSpaceInl_subset_range_opensPreimageProjLeft k M p U)`. Use `⟨IsOpenImmersion.lift (opensPreimageProjLeft k M p U).ι (U.ι ≫ affineSpaceInl k M p) (range_affineSpaceInl_subset_range_opensPreimageProjLeft k M p U), hfac, ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono (U.ι), Category.assoc, Category.id_comp, morphismRestrict_ι, ← Category.assoc, hfac, Category.assoc, affineSpaceInl_comp_projLeft, Category.comp_id]`.
-/
private theorem exists_zeroSectionOverOpen (k : Type u) [Field k] (M p : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).Opens) :
    ∃ z, z ≫ (opensPreimageProjLeft k M p U).ι = U.ι ≫ affineSpaceInl k M p ∧
      z ≫ (projLeft k M p ∣_ U) = 𝟙 _ := by
  have hfac : IsOpenImmersion.lift (opensPreimageProjLeft k M p U).ι (U.ι ≫ affineSpaceInl k M p)
        (range_affineSpaceInl_subset_range_opensPreimageProjLeft k M p U) ≫ (projLeft k M p ⁻¹ᵁ U).ι =
      U.ι ≫ affineSpaceInl k M p :=
    IsOpenImmersion.lift_fac (opensPreimageProjLeft k M p U).ι (U.ι ≫ affineSpaceInl k M p)
      (range_affineSpaceInl_subset_range_opensPreimageProjLeft k M p U)
  refine ⟨IsOpenImmersion.lift (opensPreimageProjLeft k M p U).ι (U.ι ≫ affineSpaceInl k M p)
      (range_affineSpaceInl_subset_range_opensPreimageProjLeft k M p U), hfac, ?_⟩
  rw [← cancel_mono (U.ι), Category.assoc, Category.id_comp, morphismRestrict_ι,
    ← Category.assoc, hfac, Category.assoc, affineSpaceInl_comp_projLeft, Category.comp_id]

def zeroSectionOverOpen (k : Type u) [Field k] (M p : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).Opens) :=
  (exists_zeroSectionOverOpen k M p U).choose

@[simp]
/- English proof (translation)
The claim follows from `(exists_zeroSectionOverOpen k M p U).choose_spec.1 @[simp]`.
-/
theorem zeroSectionOverOpen_comp_ι (k : Type u) [Field k] (M p : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).Opens) :
    zeroSectionOverOpen k M p U ≫ (opensPreimageProjLeft k M p U).ι = U.ι ≫ affineSpaceInl k M p :=
  (exists_zeroSectionOverOpen k M p U).choose_spec.1

@[simp]
/- English proof (translation)
Rewrite using `[← Category.assoc, zeroSectionOverOpen_comp_ι, Category.assoc]`. Use the proof step `@[simp]`.
-/
theorem zeroSectionOverOpen_comp_ι_assoc (k : Type u) [Field k] (M p : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).Opens) {Z : Scheme.{u}}
    (g : affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin p)) ⟶ Z) :
    zeroSectionOverOpen k M p U ≫ (opensPreimageProjLeft k M p U).ι ≫ g = U.ι ≫ affineSpaceInl k M p ≫ g := by
  rw [← Category.assoc, zeroSectionOverOpen_comp_ι, Category.assoc]

@[simp]
/- English proof (translation)
The claim follows from `(exists_zeroSectionOverOpen k M p U).choose_spec.2 @[simp]`.
-/
theorem zeroSectionOverOpen_comp_restrict (k : Type u) [Field k] (M p : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).Opens) :
    zeroSectionOverOpen k M p U ≫ (projLeft k M p ∣_ U) = 𝟙 _ :=
  (exists_zeroSectionOverOpen k M p U).choose_spec.2

@[simp]
/- English proof (translation)
Rewrite using `[← Category.assoc, zeroSectionOverOpen_comp_restrict, Category.id_comp]`.
-/
theorem zeroSectionOverOpen_comp_restrict_assoc (k : Type u) [Field k] (M p : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).Opens) {Z : Scheme.{u}}
    (g : (U : Scheme.{u}) ⟶ Z) :
    zeroSectionOverOpen k M p U ≫ (projLeft k M p ∣_ U) ≫ g = g := by
  rw [← Category.assoc, zeroSectionOverOpen_comp_restrict, Category.id_comp]

/- English proof (translation)
Establish `hcomm : zeroSectionOverOpen k M p U ≫ prodMapOnPreimage k M p c U q = q ≫ affineSpaceInl k c p`. Use `(isPullback_projLeft_projRight k c p).hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, ← morphismRestrict_projLeft_comp k M p c U q hq]`. Simplify using the standard rewrite rules. Rewrite using `[Category.assoc, prodMapOnPreimage_comp_projRight, zeroSectionOverOpen_comp_ι_assoc, affineSpaceInl_comp_projRight, Category.assoc, affineSpaceInl_comp_projRight, ← Category.assoc, ← Category.assoc, hq]`.

Establish `hs : IsPullback (zeroSectionOverOpen k M p U ≫ (projLeft k M p ∣_ U)) q q (affineSpaceInl k c p ≫ projLeft k c p)`. Rewrite using `[zeroSectionOverOpen_comp_restrict, affineSpaceInl_comp_projLeft]`. Conclude with `IsPullback.of_horiz_isIso ⟨by simp⟩`. Conclude with `IsPullback.of_right hs hcomm (isPullback_prodMapOnPreimage k M p c U q hq).flip`.
-/
theorem isPullback_zeroSectionOverOpen (k : Type u) [Field k] (M p c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).Opens)
    (q : ↑U ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin c)))
    (hq : q ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin c)) =
      U.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) :
    IsPullback (zeroSectionOverOpen k M p U) q (prodMapOnPreimage k M p c U q) (affineSpaceInl k c p) := by
  have hcomm : zeroSectionOverOpen k M p U ≫ prodMapOnPreimage k M p c U q = q ≫ affineSpaceInl k c p := by
    refine (isPullback_projLeft_projRight k c p).hom_ext ?_ ?_
    · rw [Category.assoc, ← morphismRestrict_projLeft_comp k M p c U q hq]
      simp
    · rw [Category.assoc, prodMapOnPreimage_comp_projRight, zeroSectionOverOpen_comp_ι_assoc,
        affineSpaceInl_comp_projRight, Category.assoc, affineSpaceInl_comp_projRight,
        ← Category.assoc, ← Category.assoc, hq]
  have hs : IsPullback (zeroSectionOverOpen k M p U ≫ (projLeft k M p ∣_ U)) q q
      (affineSpaceInl k c p ≫ projLeft k c p) := by
    rw [zeroSectionOverOpen_comp_restrict, affineSpaceInl_comp_projLeft]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact IsPullback.of_right hs hcomm (isPullback_prodMapOnPreimage k M p c U q hq).flip

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem pullbackCoord_comp_eq_appTop {k : Type u} [Field k] {T Y : Scheme.{u}}
    {n : Type u} (a : T ⟶ Y) (g : Y ⟶ affineSpaceIndexedBy k n) (i : n) :
    pullbackCoord (a ≫ g) i = a.appTop (pullbackCoord g i) := rfl

def uliftFinSumEquiv (c p : ℕ) : ULift.{u, 0} (Fin c ⊕ Fin p) ≃ ULift.{u, 0} (Fin (c + p)) :=
  Equiv.ulift.trans (finSumFinEquiv.trans Equiv.ulift.symm)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uliftFinSumEquiv_inl (c p : ℕ) (i : Fin c) :
    uliftFinSumEquiv.{u} c p ⟨Sum.inl i⟩ = ⟨Fin.castAdd p i⟩ :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uliftFinSumEquiv_inr (c p : ℕ) (j : Fin p) :
    uliftFinSumEquiv.{u} c p ⟨Sum.inr j⟩ = ⟨Fin.natAdd c j⟩ :=
  rfl

/- English proof (translation)
Simplify using `[pullbackCoord]`.
-/
private theorem pullbackCoord_affineSpaceIsoOfEquiv_hom (k : Type u) [Field k] {n m : Type u}
    (e : n ≃ m) (i : m) :
    pullbackCoord (affineSpaceIsoOfEquiv e (Spec (CommRingCat.of k))).hom i =
      AffineSpace.coord (Spec (CommRingCat.of k)) (e.symm i) := by
  simp [pullbackCoord]

/- English proof (translation)
Use `eq_affineSpaceOrigin_of_pullbackCoord_eq_zero k (c + p) _ ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `i`. Take `⟨j, rfl⟩ : ∃ j, i = uliftFinSumEquiv.{u} c p j` from `⟨(uliftFinSumEquiv.{u} c p).symm i, ((uliftFinSumEquiv.{u} c p).apply_symm_apply i).symm⟩`. Establish `h1 : pullbackCoord (affineSpaceInl k c p ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom) (uliftFinSumEquiv.{u} c p j) = pullbackCoord (affineSpaceInl k c p) j`.

Rewrite using `[pullbackCoord_comp_eq_appTop, pullbackCoord_affineSpaceIsoOfEquiv_hom, Equiv.symm_apply_apply, pullbackCoord_def]`. Rewrite using `[pullbackCoord_comp_eq_appTop, h1]`. Take `⟨a | b⟩` from `j`. Rewrite using `[pullbackCoord_affineSpaceInl_inl]`. Conclude with `affineSpaceOrigin_appTop_coord k c (ULift.up a)`.

Rewrite using `[pullbackCoord_affineSpaceInl_inr]`. Simplify using the standard rewrite rules.
-/
theorem affineSpaceOrigin_comp_affineSpaceInl_affineSpaceIsoOfEquiv (k : Type u) [Field k] (c p : ℕ) :
    affineSpaceOrigin k c ≫ affineSpaceInl k c p ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom =
      affineSpaceOrigin k (c + p) := by
  refine eq_affineSpaceOrigin_of_pullbackCoord_eq_zero k (c + p) _ ?_ ?_
  · simp
  · intro i
    obtain ⟨j, rfl⟩ : ∃ j, i = uliftFinSumEquiv.{u} c p j :=
      ⟨(uliftFinSumEquiv.{u} c p).symm i, ((uliftFinSumEquiv.{u} c p).apply_symm_apply i).symm⟩
    have h1 : pullbackCoord (affineSpaceInl k c p ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom)
          (uliftFinSumEquiv.{u} c p j) = pullbackCoord (affineSpaceInl k c p) j := by
      rw [pullbackCoord_comp_eq_appTop, pullbackCoord_affineSpaceIsoOfEquiv_hom,
        Equiv.symm_apply_apply, pullbackCoord_def]
    rw [pullbackCoord_comp_eq_appTop, h1]
    obtain ⟨a | b⟩ := j
    · rw [pullbackCoord_affineSpaceInl_inl]
      exact affineSpaceOrigin_appTop_coord k c (ULift.up a)
    · rw [pullbackCoord_affineSpaceInl_inr]
      simp

namespace HasSmoothCoordCodim

/- English proof (translation)
Rewrite using `[← H.flip.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]`.
-/
private theorem ker_eq_comap_ker_of_isPullback_closedImmersion {Z X X' W : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (g : X' ⟶ X) (j : W ⟶ X') (a : W ⟶ Z)
    (H : IsPullback a j i g) :
    Scheme.Hom.ker j = (Scheme.Hom.ker i).comap g := by
  rw [← H.flip.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/- English proof (translation)
Introduce `x`. Take `⟨U, hxU, q, hqsm, hqcomp, hker⟩` from `h x`. Establish `: AlgebraicGeometry.Smooth q` using `hqsm`. Establish `hker' : (Scheme.Hom.ker ρ).comap U.ι = (coordSubspaceIdeal k c Finset.univ).comap q` using `hker`. Establish `hs : IsPullback (zeroSectionOverOpen k M p U ≫ (projLeft k M p ∣_ U)) U.ι U.ι (affineSpaceInl k M p ≫ projLeft k M p)`.

Rewrite using `[zeroSectionOverOpen_comp_restrict, affineSpaceInl_comp_projLeft]`. Conclude with `IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩`. Establish `hA : IsPullback (zeroSectionOverOpen k M p U) U.ι (opensPreimageProjLeft k M p U).ι (affineSpaceInl k M p)` using `IsPullback.of_right hs (zeroSectionOverOpen_comp_ι k M p U) (isPullback_morphismRestrict (projLeft k M p) U)`. Take `⟨a₀, hB⟩` from `exists_isPullback_of_ker_eq_comap ρ ((Scheme.Hom.ker ρ).comap U.ι).subschemeι U.ι (Scheme.IdealSheafData.ker_subschemeι ..)`. Establish `hW1` using `hB.flip.paste_horiz hA`.

Establish `hB2 : Scheme.Hom.ker ((Scheme.Hom.ker ρ).comap U.ι).subschemeι = (Scheme.Hom.ker (affineSpaceOrigin k c)).comap q`. Rewrite using `[Scheme.IdealSheafData.ker_subschemeι, ker_affineSpaceOrigin]`. Conclude with `hker'`. Take `⟨c₁, hC⟩` from `exists_isPullback_of_ker_eq_comap (affineSpaceOrigin k c) ((Scheme.Hom.ker ρ).comap U.ι).subschemeι q hB2`. Establish `hW2` using `hC.flip.paste_horiz (isPullback_zeroSectionOverOpen k M p c U q hqcomp)`.

Establish `hRsq : IsPullback (𝟙 (opensPreimageProjLeft k M p U).toScheme) (prodMapOnPreimage k M p c U q) (prodMapOnPreimage k M p c U q ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom) (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.o …` using `IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp]⟩`. Establish `hσR : (affineSpaceOrigin k c ≫ affineSpaceInl k c p) ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom = affineSpaceOrigin k (c + p)`. Rewrite using `[Category.assoc, affineSpaceOrigin_comp_affineSpaceInl_affineSpaceIsoOfEquiv]`. Establish `hW3` using `hW2.paste_horiz hRsq`. Rewrite `hW3` using `[Category.comp_id, hσR]`.

Use `⟨opensPreimageProjLeft k M p U, ?_, prodMapOnPreimage k M p c U q ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (projLeft k M p) ((ρ ≫ affineSpaceInl k M p) x) ∈ U`. Establish `hx1 : (projLeft k M p) ((ρ ≫ affineSpaceInl k M p) x) = ρ x` using `congrArg (fun f : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) => ⇑f x) (show (ρ ≫ affineSpaceInl k M p) ≫ projLeft k M p = ρ by`. Rewrite using `[Category.assoc, affineSpaceInl_comp_projLeft, Category.comp_id])`. Rewrite using `[hx1]`.

Conclude with `hxU`. Establish `: AlgebraicGeometry.Smooth (prodMapOnPreimage k M p c U q)` using `smooth_prodMapOnPreimage hsm k M p c U q hqcomp infer_instance`. Rewrite using `[Category.assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec]`. Use `show (Scheme.Hom.ker (ρ ≫ affineSpaceInl k M p)).comap (opensPreimageProjLeft k M p U).ι = (coordSubspaceIdeal k (c + p) Finset.univ).comap (prodMapOnPreimage k M p c U q ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom)`. Rewrite using `[← ker_eq_comap_ker_of_isPullback_closedImmersion (ρ ≫ affineSpaceInl k M p) (opensPreimageProjLeft k M p U).ι _ _ hW1.flip, ker_eq_comap_ker_of_isPullback_closedImmersion (affineSpaceOrigin k (c + p)) (prodMapOnPreimage k M p c U q ≫ (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} …`.
-/
theorem comp_affineSpaceInl (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] {M c : ℕ} {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ] (p : ℕ)
    (h : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) ρ c) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin p)))
      (ρ ≫ affineSpaceInl k M p) (c + p) := by
  intro x
  obtain ⟨U, hxU, q, hqsm, hqcomp, hker⟩ := h x
  have : AlgebraicGeometry.Smooth q := hqsm
  have hker' : (Scheme.Hom.ker ρ).comap U.ι = (coordSubspaceIdeal k c Finset.univ).comap q := hker
  have hs : IsPullback (zeroSectionOverOpen k M p U ≫ (projLeft k M p ∣_ U)) U.ι U.ι
      (affineSpaceInl k M p ≫ projLeft k M p) := by
    rw [zeroSectionOverOpen_comp_restrict, affineSpaceInl_comp_projLeft]
    exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  have hA : IsPullback (zeroSectionOverOpen k M p U) U.ι (opensPreimageProjLeft k M p U).ι (affineSpaceInl k M p) :=
    IsPullback.of_right hs (zeroSectionOverOpen_comp_ι k M p U)
      (isPullback_morphismRestrict (projLeft k M p) U)
  obtain ⟨a₀, hB⟩ := exists_isPullback_of_ker_eq_comap ρ
    ((Scheme.Hom.ker ρ).comap U.ι).subschemeι U.ι (Scheme.IdealSheafData.ker_subschemeι ..)
  have hW1 := hB.flip.paste_horiz hA
  have hB2 : Scheme.Hom.ker ((Scheme.Hom.ker ρ).comap U.ι).subschemeι =
      (Scheme.Hom.ker (affineSpaceOrigin k c)).comap q := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ker_affineSpaceOrigin]
    exact hker'
  obtain ⟨c₁, hC⟩ := exists_isPullback_of_ker_eq_comap (affineSpaceOrigin k c)
    ((Scheme.Hom.ker ρ).comap U.ι).subschemeι q hB2
  have hW2 := hC.flip.paste_horiz (isPullback_zeroSectionOverOpen k M p c U q hqcomp)
  have hRsq : IsPullback (𝟙 (opensPreimageProjLeft k M p U).toScheme) (prodMapOnPreimage k M p c U q)
      (prodMapOnPreimage k M p c U q ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom)
      (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp]⟩
  have hσR : (affineSpaceOrigin k c ≫ affineSpaceInl k c p) ≫
      (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom =
      affineSpaceOrigin k (c + p) := by
    rw [Category.assoc, affineSpaceOrigin_comp_affineSpaceInl_affineSpaceIsoOfEquiv]
  have hW3 := hW2.paste_horiz hRsq
  rw [Category.comp_id, hσR] at hW3
  refine ⟨opensPreimageProjLeft k M p U, ?_, prodMapOnPreimage k M p c U q ≫
      (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom, ?_, ?_, ?_⟩
  · show (projLeft k M p) ((ρ ≫ affineSpaceInl k M p) x) ∈ U
    have hx1 : (projLeft k M p) ((ρ ≫ affineSpaceInl k M p) x) = ρ x :=
      congrArg (fun f : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) => ⇑f x)
        (show (ρ ≫ affineSpaceInl k M p) ≫ projLeft k M p = ρ by
          rw [Category.assoc, affineSpaceInl_comp_projLeft, Category.comp_id])
    rw [hx1]
    exact hxU
  · have : AlgebraicGeometry.Smooth (prodMapOnPreimage k M p c U q) :=
      smooth_prodMapOnPreimage hsm k M p c U q hqcomp
    infer_instance
  · rw [Category.assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec]
  · show (Scheme.Hom.ker (ρ ≫ affineSpaceInl k M p)).comap (opensPreimageProjLeft k M p U).ι =
      (coordSubspaceIdeal k (c + p) Finset.univ).comap (prodMapOnPreimage k M p c U q ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom)
    rw [← ker_eq_comap_ker_of_isPullback_closedImmersion (ρ ≫ affineSpaceInl k M p)
        (opensPreimageProjLeft k M p U).ι _ _ hW1.flip,
      ker_eq_comap_ker_of_isPullback_closedImmersion (affineSpaceOrigin k (c + p))
        (prodMapOnPreimage k M p c U q ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} c p) (Spec (CommRingCat.of k))).hom) _ _ hW3.flip,
      ker_affineSpaceOrigin]

/- English proof (translation)
Establish `h1` using `comp_affineSpaceInl hsm k ρ p h`. Establish `h2` using `h1.comp_iso_hom (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M p) (Spec (CommRingCat.of k))) (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + p)))) (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumEquiv.{u} M p))`. Rewrite `h2` using `[Category.assoc]`. Then use the resulting hypothesis.
-/
theorem comp_affineSpaceInl_affineSpaceIsoOfEquiv (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] {M c : ℕ} {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ] (p : ℕ)
    (h : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) ρ c) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + p))))
      (ρ ≫ affineSpaceInl k M p ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M p) (Spec (CommRingCat.of k))).hom) (c + p) := by
  have h1 := comp_affineSpaceInl hsm k ρ p h
  have h2 := h1.comp_iso_hom
    (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M p) (Spec (CommRingCat.of k)))
    (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + p))))
    (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumEquiv.{u} M p))
  rwa [Category.assoc] at h2

end HasSmoothCoordCodim

end FunctorialResolution.EmbeddedResolution

end
