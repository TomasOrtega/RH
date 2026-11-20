import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactReduction

namespace FiniteOpenCoverWithIdeals

variable {T : MarkedIdealWithBoundary.{u}}

abbrev piece (D : FiniteOpenCoverWithIdeals T) (i : D.idx) : Scheme.{u} := (D.opens i).toScheme

abbrev summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) : D.piece i ⟶ D.disjointUnion :=
  Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i

/- English proof (authored)
The summand inclusion of a scheme coproduct identifies its source with an open subscheme, namely the component corresponding to that summand.
-/
theorem isOpenImmersion_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsOpenImmersion (D.summandι i) := by
  show IsOpenImmersion (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i)
  infer_instance

instance instIsOpenImmersionSummandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsOpenImmersion (D.summandι i) :=
  isOpenImmersion_summandι D i

/- English proof (authored)
A summand of the disjoint union is an open and closed subscheme with the induced structure sheaf. Its coproduct inclusion is therefore also a closed immersion.
-/
theorem isClosedImmersion_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsClosedImmersion (D.summandι i) := by
  show IsClosedImmersion (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i)
  infer_instance

instance instIsClosedImmersionSummandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsClosedImmersion (D.summandι i) :=
  isClosedImmersion_summandι D i

/- English proof (authored)
The inclusion is that of an open and closed summand. Its inverse image of a quasi-compact open is a closed subset of that open and is therefore quasi-compact.
-/
theorem quasiCompact_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    QuasiCompact (D.summandι i) := by
  show QuasiCompact (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i)
  infer_instance

instance instQuasiCompactSummandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    QuasiCompact (D.summandι i) :=
  quasiCompact_summandι D i

/- English proof (authored)
The map from the coproduct is determined by the original open inclusions on its summands. The defining coproduct identity gives the stated composite.
-/
theorem summandι_comp_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    D.summandι i ≫ D.disjointUnionMap = (D.opens i).ι :=
  sigma_ι_sigmaOpensDesc T.scheme D.opens i

/- English proof (authored)
The composite is the inclusion of the given open into the original scheme, whose image is that open. Evaluating the composite at the summand point gives the membership.
-/
theorem disjointUnionMap_summandι_mem (D : FiniteOpenCoverWithIdeals T) (i : D.idx) (y : D.piece i) :
    D.disjointUnionMap.base ((D.summandι i).base y) ∈ D.opens i := by
  have hmem : D.disjointUnionMap.base ((D.summandι i).base y) ∈ Set.range (D.opens i).ι.base := by
    rw [← summandι_comp_disjointUnionMap D i]
    exact ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι] at hmem
  exact hmem

/- English proof (authored)
The summand inclusion is a closed immersion. The image ideal of a closed subscheme pulls back through that immersion to the original defining ideal.
-/
private theorem comap_imageIdealSheaf_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    (imageIdealSheaf (D.summandι i) (D.localIdeal i)).comap (D.summandι i) = D.localIdeal i :=
  FunctorialResolution.EmbeddedResolution.comap_ker_subschemeι_comp (D.localIdeal i) (D.summandι i)

/- English proof (authored)
By definition the image ideal is the kernel of the map from the closed subscheme to the target, obtained by composing its inclusion with the given morphism.
-/
private theorem imageIdealSheaf_eq_ker {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (I : X.IdealSheafData) : imageIdealSheaf f I = Scheme.Hom.ker (I.subschemeι ≫ f) := rfl

/- English proof (authored)
The sheaf condition for the empty cover makes the ring of sections on the empty open terminal. Its two projections from its square are therefore equal. Evaluating them on any pair of sections shows those sections are equal.
-/
private theorem subsingleton_sections_bot (Z : Scheme.{u}) :
    Subsingleton ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens))) := by
  have ht : CategoryTheory.Limits.IsTerminal (Z.presheaf.obj (Opposite.op (⊥ : Z.Opens))) :=
    TopCat.Sheaf.isTerminalOfEmpty Z.sheaf
  refine ⟨fun a b => ?_⟩
  have h := ht.hom_ext
    (CommRingCat.ofHom (RingHom.fst ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens)))
      ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens)))))
    (CommRingCat.ofHom (RingHom.snd ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens)))
      ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens)))))
  exact congrArg (fun m => (CommRingCat.Hom.hom m) (a, b)) h

/- English proof (authored)
The affine open misses the image, so its inverse image is empty. On that inverse image the section ring has one element, so the map on sections sends one to zero. The kernel ideal on the affine open thus contains one and is the unit ideal.
-/
private theorem ideal_ker_eq_top_of_disjoint {Y Z : Scheme.{u}} (g : Z ⟶ Y) [QuasiCompact g]
    (U : Y.affineOpens) (hdisj : ∀ z : ↥Z, g.base z ∉ (U.1 : Set ↥Y)) :
    (Scheme.Hom.ker g).ideal U = ⊤ := by
  have hempty : g ⁻¹ᵁ U.1 = ⊥ := by
    refine TopologicalSpace.Opens.ext ?_
    rw [TopologicalSpace.Opens.coe_bot]
    exact Set.eq_empty_iff_forall_notMem.mpr fun z hz => hdisj z hz
  have hsub : Subsingleton ↥(Z.presheaf.obj (Opposite.op (g ⁻¹ᵁ U.1))) := by
    rw [hempty]
    exact subsingleton_sections_bot Z
  rw [Scheme.Hom.ker_apply]
  refine (Ideal.eq_top_iff_one _).mpr ?_
  rw [RingHom.mem_ker, map_one]
  exact Subsingleton.elim _ _

/- English proof (authored)
The subscheme giving the image ideal maps into summand $j$, while the affine open lies in summand $i$. Distinct coproduct summands have disjoint images, so the inverse image of the affine open is empty. Its kernel ideal on that open is unit.
-/
private theorem ideal_imageIdealSheaf_eq_top_of_ne (D : FiniteOpenCoverWithIdeals T) {i j : D.idx} (hij : j ≠ i)
    (W : D.disjointUnion.Opens) (hW : IsAffineOpen W)
    (hsub : ∀ y ∈ (W : Set ↥D.disjointUnion), y ∈ Set.range (D.summandι i).base) :
    (imageIdealSheaf (D.summandι j) (D.localIdeal j)).ideal ⟨W, hW⟩ = ⊤ := by
  rw [imageIdealSheaf_eq_ker]
  refine ideal_ker_eq_top_of_disjoint ((D.localIdeal j).subschemeι ≫ D.summandι j) ⟨W, hW⟩ ?_
  intro z hz
  obtain ⟨v, hv⟩ := hsub _ hz
  have hcomp : ((D.localIdeal j).subschemeι ≫ D.summandι j).base z
      = (D.summandι j).base ((D.localIdeal j).subschemeι.base z) := rfl
  exact Blowup.sigmaι_base_ne (fun t : D.idx => (D.opens t).toScheme) hij
    ((D.localIdeal j).subschemeι.base z) v (hcomp.symm.trans hv.symm)

/- English proof (authored)
Work on an affine open of summand $i$. Its image in the disjoint union is affine because the summand inclusion is an open immersion. There all image ideals from other summands are unit, since their images are disjoint. Thus the intersection of image ideals on this affine image is the contribution from $i$ alone. Pulling it back along the summand inclusion recovers the original ideal of that summand. Equality on every affine open gives the result.
-/
theorem comap_iInfImageIdeal_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    D.iInfImageIdeal.comap (D.summandι i) = D.localIdeal i := by
  have hglue : D.iInfImageIdeal
      = ⨅ j : D.idx, imageIdealSheaf (D.summandι j) (D.localIdeal j) := rfl
  refine le_antisymm ?_ ?_
  · rw [hglue]
    exact le_trans (Scheme.IdealSheafData.comap_mono (D.summandι i) (iInf_le _ i))
      (le_of_eq (comap_imageIdealSheaf_summandι D i))
  · rw [Scheme.IdealSheafData.le_def]
    intro V
    have hW : IsAffineOpen ((D.summandι i) ''ᵁ V.1) :=
      V.2.image_of_isOpenImmersion (D.summandι i)
    have hle : V.1 ≤ (D.summandι i) ⁻¹ᵁ ((D.summandι i) ''ᵁ V.1) := fun x hx => ⟨x, hx, rfl⟩
    have hsub : ∀ y ∈ ((((D.summandι i) ''ᵁ V.1) : D.disjointUnion.Opens) : Set ↥D.disjointUnion),
        y ∈ Set.range (D.summandι i).base := by
      rintro y ⟨v, hv, rfl⟩
      exact ⟨v, rfl⟩
    have h1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE D.iInfImageIdeal (D.summandι i)
      ⟨_, hW⟩ V hle
    have h2 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE
      (imageIdealSheaf (D.summandι i) (D.localIdeal i)) (D.summandι i) ⟨_, hW⟩ V hle
    have h3 : D.iInfImageIdeal.ideal ⟨_, hW⟩
        = (imageIdealSheaf (D.summandι i) (D.localIdeal i)).ideal ⟨_, hW⟩ := by
      rw [hglue]
      simp only [Scheme.IdealSheafData.ideal_iInf, iInf_apply]
      refine le_antisymm (iInf_le _ i) (le_iInf fun j => ?_)
      by_cases hj : j = i
      · rw [hj]
      · rw [ideal_imageIdealSheaf_eq_top_of_ne D hj _ hW hsub]
        exact le_top
    have h4 : (D.iInfImageIdeal.comap (D.summandι i)).ideal V = (D.localIdeal i).ideal V := by
      rw [h1, h3, ← h2, comap_imageIdealSheaf_summandι D i]
    exact le_of_eq h4.symm

abbrev summandOpen (D : FiniteOpenCoverWithIdeals T) (i : D.idx) : D.disjointUnion.Opens :=
  (D.summandι i).opensRange

/- English proof (authored)
The associated summand open is defined to be the image of the summand inclusion. The inclusion of this open has that same image.
-/
theorem range_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    Set.range (D.summandι i).base = Set.range (D.summandOpen i).ι.base :=
  (Scheme.Opens.range_ι (D.summandOpen i)).symm

abbrev summandIso (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    D.piece i ≅ (D.summandOpen i).toScheme :=
  IsOpenImmersion.isoOfRangeEq (D.summandι i) (D.summandOpen i).ι (range_summandι D i)

/- English proof (authored)
Identify the summand open with the original summand by the inverse of the image isomorphism. Its inclusion then factors through the coproduct summand inclusion. Composing with the total map gives the original open inclusion.
-/
theorem summandOpen_ι_comp_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    (D.summandOpen i).ι ≫ D.disjointUnionMap = (D.summandIso i).inv ≫ (D.opens i).ι := by
  have h : (D.summandIso i).inv ≫ D.summandι i = (D.summandOpen i).ι := by
    simp [FiniteOpenCoverWithIdeals.summandIso]
  rw [← h, Category.assoc, summandι_comp_disjointUnionMap]

/- English proof (authored)
The underlying point space of the scheme coproduct is the disjoint union of the summand point spaces. Represent the point by a summand index and a point in that summand. Its image under the corresponding inclusion is the given point.
-/
theorem exists_summandι_base_eq (D : FiniteOpenCoverWithIdeals T) (x : ↥D.disjointUnion) :
    ∃ (i : D.idx) (y : D.piece i), (D.summandι i).base y = x := by
  obtain ⟨⟨i, y⟩, hx⟩ := (sigmaMk fun j : D.idx => (D.opens j).toScheme).surjective x
  refine ⟨i, y, ?_⟩
  show (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i).base y = x
  simpa using hx

/- English proof (authored)
Represent the point as the image of a summand point. This puts it in the range of that summand inclusion, which is the designated summand open.
-/
theorem exists_mem_summandOpen (D : FiniteOpenCoverWithIdeals T) (x : ↥D.disjointUnion) :
    ∃ i : D.idx, x ∈ D.summandOpen i := by
  obtain ⟨i, y, hy⟩ := D.exists_summandι_base_eq x
  refine ⟨i, ?_⟩
  have hmem : x ∈ Set.range (D.summandι i).base := ⟨y, hy⟩
  exact hmem

/- English proof (authored)
The scheme of the original open is affine by hypothesis. Its image under the coproduct open immersion is isomorphic to it, so the resulting summand open is affine.
-/
theorem isAffineOpen_summandOpen (D : FiniteOpenCoverWithIdeals T) (i : D.idx) (h : IsAffineOpen (D.opens i)) :
    IsAffineOpen (D.summandOpen i) := by
  have hA : IsAffine ((D.opens i).toScheme) := h
  exact isAffineOpen_opensRange (D.summandι i)

/- English proof (authored)
The inclusion of the summand open is its inverse image isomorphism to the summand followed by the coproduct inclusion. Restriction is pullback along that composite, which factors into the two stated pullbacks.
-/
theorem restrictIdeal_summandOpen (D : FiniteOpenCoverWithIdeals T) (i : D.idx) (J : D.disjointUnion.IdealSheafData) :
    restrictIdeal J (D.summandOpen i) = (J.comap (D.summandι i)).comap (D.summandIso i).inv := by
  have h : (D.summandIso i).inv ≫ D.summandι i = (D.summandOpen i).ι := by
    simp [FiniteOpenCoverWithIdeals.summandIso]
  rw [restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp, h]

/- English proof (authored)
Express restriction to the summand open as pullback to the summand followed by transport along the inverse image isomorphism. The first pullback of the assembled ideal is the original local ideal, leaving its stated transport.
-/
theorem restrictIdeal_iInfImageIdeal_summandOpen (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    restrictIdeal D.iInfImageIdeal (D.summandOpen i) =
      (D.localIdeal i).comap (D.summandIso i).inv := by
  rw [restrictIdeal_summandOpen D i D.iInfImageIdeal, comap_iInfImageIdeal_summandι D i]

/- English proof (authored)
The assembled ideal is defined as the intersection of the image ideals of all the summand ideals.
-/
theorem iInfImageIdeal_eq_iInf (D : FiniteOpenCoverWithIdeals T) :
    D.iInfImageIdeal = ⨅ i : D.idx, imageIdealSheaf (D.summandι i) (D.localIdeal i) :=
  rfl

/- English proof (authored)
Use functoriality to write the left side as pullback along the summand open inclusion followed by the total map. This composite is the inverse summand isomorphism followed by the original open inclusion. Pulling back in that order gives the right side.
-/
theorem restrictIdeal_comap_disjointUnionMap_summandOpen (D : FiniteOpenCoverWithIdeals T) (i : D.idx)
    (J : T.scheme.IdealSheafData) :
    restrictIdeal (J.comap D.disjointUnionMap) (D.summandOpen i) =
      (restrictIdeal J (D.opens i)).comap (D.summandIso i).inv := by
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, summandOpen_ι_comp_disjointUnionMap]

/- English proof (authored)
The original chart followed by the affine-space structure map agrees with the original open's map to the field. Precompose by the inverse summand isomorphism. The resulting map to the original scheme is the summand open inclusion followed by the total cover map, giving the claimed structure map.
-/
private theorem summandIso_inv_comp_map_comp_affineSpaceFinToSpec (D : FiniteOpenCoverWithIdeals T) (i : D.idx) {n : ℕ}
    (c : EtaleChart T.structMap (D.opens i) n) :
    ((D.summandIso i).inv ≫ c.map) ≫ affineSpaceFinToSpec T.base n =
      (D.summandOpen i).ι ≫ (D.disjointUnionMap ≫ T.structMap) := by
  rw [Category.assoc, c.comp_struct, ← Category.assoc, ← summandOpen_ι_comp_disjointUnionMap,
    Category.assoc]

/- English proof (authored)
The inverse summand isomorphism is étale, as is the original chart map. Étale morphisms are closed under composition.
-/
private theorem etale_summandIso_inv_comp_map (D : FiniteOpenCoverWithIdeals T) (i : D.idx) {n : ℕ}
    (c : EtaleChart T.structMap (D.opens i) n) :
    Etale ((D.summandIso i).inv ≫ c.map) := by
  have h1 : Etale c.map := c.isEtale
  have h4 : Etale ((D.summandIso i).inv) := inferInstance
  infer_instance

def summandEtaleChart (D : FiniteOpenCoverWithIdeals T) (i : D.idx) {n : ℕ}
    (c : EtaleChart T.structMap (D.opens i) n) :
    EtaleChart (D.disjointUnionMap ≫ T.structMap) (D.summandOpen i) n where
  map := (D.summandIso i).inv ≫ c.map
  comp_struct := summandIso_inv_comp_map_comp_affineSpaceFinToSpec D i c
  isEtale := etale_summandIso_inv_comp_map D i c

/- English proof (authored)
The transported chart map is defined by first identifying the summand open with the original open and then using the given chart map.
-/
theorem summandEtaleChart_map (D : FiniteOpenCoverWithIdeals T) (i : D.idx) {n : ℕ}
    (c : EtaleChart T.structMap (D.opens i) n) :
    (D.summandEtaleChart i c).map = (D.summandIso i).inv ≫ c.map := rfl

/- English proof (authored)
Each coordinate ideal is the pullback of the corresponding coordinate-subspace ideal on affine space. The transported chart map is the inverse summand isomorphism followed by the original chart map. Functoriality writes its coordinate ideal as the original coordinate ideal pulled back along the inverse isomorphism.
-/
theorem summandEtaleChart_coordIdeal (D : FiniteOpenCoverWithIdeals T) (i : D.idx) {n : ℕ}
    (c : EtaleChart T.structMap (D.opens i) n) (S : Finset (Fin n)) :
    (D.summandEtaleChart i c).coordIdeal S = (c.coordIdeal S).comap (D.summandIso i).inv := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, summandEtaleChart_map,
    ← Scheme.IdealSheafData.comap_comp]

/- English proof (authored)
For any element of one ideal, its image belongs to the common image ideal. Surjectivity of the ring map realizes that image as the image of an element of the other original ideal. Injectivity makes the two original elements equal. This proves both inclusions by interchanging the ideals.
-/
private theorem eq_of_map_eq_of_bijective {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hinj : Function.Injective φ) (hsurj : Function.Surjective φ)
    {I I' : Ideal A} (h : Ideal.map φ I = Ideal.map φ I') : I = I' := by
  ext x
  constructor
  · intro hx
    have hmem : φ x ∈ Ideal.map φ I' := by
      rw [← h]
      exact Ideal.mem_map_of_mem φ hx
    obtain ⟨a, ha, hax⟩ := (Ideal.mem_map_iff_of_surjective (f := φ) hsurj).mp hmem
    have hax' : a = x := hinj hax
    rw [hax'] at ha
    exact ha
  · intro hx
    have hmem : φ x ∈ Ideal.map φ I := by
      rw [h]
      exact Ideal.mem_map_of_mem φ hx
    obtain ⟨a, ha, hax⟩ := (Ideal.mem_map_iff_of_surjective (f := φ) hsurj).mp hmem
    have hax' : a = x := hinj hax
    rw [hax'] at ha
    exact ha

/- English proof (authored)
Every point of the open subscheme is a point of the ambient scheme lying in the given open. Thus the preimage of that open under its own inclusion contains the whole open subscheme.
-/
private theorem top_le_preimage_opens {X : Scheme.{u}} (V : X.Opens) :
    (⊤ : V.toScheme.Opens) ≤ (TopologicalSpace.Opens.map V.ι.base).obj V := by
  intro y _
  exact y.2

/- English proof (authored)
On sections, the open inclusion identifies the original sections over the given open with the global sections of the corresponding open subscheme. The ring map in this direction is the inverse of the canonical identification from the global sections to the original section ring.
-/
private theorem appLE_ι_eq_topIso_inv {X : Scheme.{u}} (V : X.Opens) :
    V.ι.appLE V ⊤ (top_le_preimage_opens V) = V.topIso.inv := by
  simp
  rfl

/- English proof (authored)
Evaluate the two pulled-back ideals on the whole affine open subscheme. These evaluations are the images of the original ideals on that affine open under its section-ring isomorphism. They agree by hypothesis. A ring isomorphism reflects equality of ideals, so the original ideals agree there.
-/
private theorem ideal_eq_of_comap_ι_eq {X : Scheme.{u}} {I J : X.IdealSheafData}
    (V : X.Opens) (hV : IsAffineOpen V) (h : I.comap V.ι = J.comap V.ι) :
    I.ideal ⟨V, hV⟩ = J.ideal ⟨V, hV⟩ := by
  have : IsAffine V.toScheme := hV
  have key1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE I V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_preimage_opens V)
  have key2 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE J V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_preimage_opens V)
  rw [h] at key1
  have hinj : Function.Injective
      (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_preimage_opens V))) := by
    rw [appLE_ι_eq_topIso_inv V]
    exact V.topIso.symm.commRingCatIsoToRingEquiv.injective
  have hsurj : Function.Surjective
      (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_preimage_opens V))) := by
    rw [appLE_ι_eq_topIso_inv V]
    exact V.topIso.symm.commRingCatIsoToRingEquiv.surjective
  exact eq_of_map_eq_of_bijective _ hinj hsurj (key1.symm.trans key2)

/- English proof (authored)
Refine the given open cover by all affine opens contained in one of its members. They still cover the scheme because affine opens form a basis. On each of them the pulled-back ideals agree by factoring its inclusion through the original cover member. The affine evaluation result gives equality of the ideals on that affine open. The resulting local equalities imply equality globally.
-/
private theorem ext_of_comap_ι_eq_of_iSup_eq_top {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (hU : iSup U = ⊤) {I J : X.IdealSheafData}
    (h : ∀ i : ι, I.comap (U i).ι = J.comap (U i).ι) : I = J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := {W : X.affineOpens // ∃ i : ι, (W.1 : X.Opens) ≤ U i})
    (fun W => W.1) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ iSup U := by
      rw [hU]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨V, hV, hxV, hVU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hi
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, i, hVU⟩, hxV⟩
  · rintro ⟨⟨W, hW⟩, i, hWU⟩
    refine ideal_eq_of_comap_ι_eq W hW ?_
    have e1 : I.comap W.ι = (I.comap (U i).ι).comap (X.homOfLE hWU) := by
      rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]
    have e2 : J.comap W.ι = (J.comap (U i).ι).comap (X.homOfLE hWU) := by
      rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]
    rw [e1, e2, h i]

/- English proof (authored)
The summand opens cover the disjoint union. On each summand open, restriction of each ideal is its given summand pullback transported by the same isomorphism. These restrictions agree by hypothesis, and equality of ideals can be checked on an open cover.
-/
theorem ext_of_comap_summandι (D : FiniteOpenCoverWithIdeals T) {J J' : D.disjointUnion.IdealSheafData}
    (h : ∀ i : D.idx, J.comap (D.summandι i) = J'.comap (D.summandι i)) : J = J' := by
  refine ext_of_comap_ι_eq_of_iSup_eq_top (fun i : D.idx => D.summandOpen i) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := D.exists_mem_summandOpen x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    have h1 := restrictIdeal_summandOpen D i J
    have h2 := restrictIdeal_summandOpen D i J'
    rw [h i] at h1
    exact h1.trans h2.symm

/- English proof (authored)
Take an element of the first ideal. Its image lies in the image of the second ideal by the assumed inclusion. Surjectivity expresses it as the image of an element of that ideal, and injectivity identifies the two preimages. This proves the original inclusion.
-/
private theorem ideal_le_of_map_le_of_bijective {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hinj : Function.Injective φ) (hsurj : Function.Surjective φ)
    {I I' : Ideal A} (h : Ideal.map φ I ≤ Ideal.map φ I') : I ≤ I' := by
  intro a ha
  have h1 : φ a ∈ Ideal.map φ I' := h (Ideal.mem_map_of_mem φ ha)
  obtain ⟨b, hb, hba⟩ := (Ideal.mem_map_iff_of_surjective (f := φ) hsurj).mp h1
  have hba' : b = a := hinj hba
  rwa [hba'] at hb

/- English proof (authored)
Evaluate the pullback inclusion on the whole affine open subscheme. The two evaluated ideals are the images of the original affine ideals under a ring isomorphism. This isomorphism reflects inclusion, giving the claimed inequality.
-/
private theorem ideal_le_of_comap_ι_le {Y : Scheme.{u}} {J J' : Y.IdealSheafData}
    (V : Y.Opens) (hV : IsAffineOpen V) (h : J.comap V.ι ≤ J'.comap V.ι) :
    J.ideal ⟨V, hV⟩ ≤ J'.ideal ⟨V, hV⟩ := by
  have : IsAffine V.toScheme := hV
  have k1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE J V.ι ⟨V, hV⟩
    ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_preimage_opens V)
  have k2 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE J' V.ι ⟨V, hV⟩
    ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_preimage_opens V)
  have hle := Scheme.IdealSheafData.le_def.mp h ⟨⊤, isAffineOpen_top V.toScheme⟩
  rw [k1, k2, appLE_ι_eq_topIso_inv V] at hle
  have hinj : Function.Injective (CommRingCat.Hom.hom V.topIso.inv) :=
    V.topIso.symm.commRingCatIsoToRingEquiv.injective
  have hsurj : Function.Surjective (CommRingCat.Hom.hom V.topIso.inv) :=
    V.topIso.symm.commRingCatIsoToRingEquiv.surjective
  exact ideal_le_of_map_le_of_bijective _ hinj hsurj hle

/- English proof (authored)
Refine the pointwise neighborhoods by affine opens, which still cover the scheme. On each of these affine opens the first ideal is contained in the second, so their intersection equals the first ideal. Equality of ideal sheaves can be checked on the affine cover. Thus the intersection is the first ideal globally, which is equivalent to the desired inclusion.
-/
private theorem le_of_ideal_le_locally {Y : Scheme.{u}} {J J' : Y.IdealSheafData}
    (V : ↥Y → Y.Opens) (hmem : ∀ y : ↥Y, y ∈ V y)
    (hloc : ∀ (y : ↥Y) (W : Y.Opens) (hW : IsAffineOpen W), W ≤ V y →
      J.ideal ⟨W, hW⟩ ≤ J'.ideal ⟨W, hW⟩) :
    J ≤ J' := by
  have key : J ⊓ J' = J := by
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top
      (ι := {W : Y.affineOpens // ∃ y : ↥Y, (W.1 : Y.Opens) ≤ V y})
      (fun W => W.1) ?_ ?_
    · rw [eq_top_iff]
      intro x _
      obtain ⟨W, hW, hxW, hWV⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (hmem x)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, x, hWV⟩, hxW⟩
    · rintro ⟨⟨W, hW⟩, y, hWV⟩
      show (J ⊓ J').ideal ⟨W, hW⟩ = J.ideal ⟨W, hW⟩
      simp only [Scheme.IdealSheafData.ideal_inf, Pi.inf_apply, inf_eq_left]
      exact hloc y W hW hWV
  exact inf_eq_left.mp key

/- English proof (authored)
For every point choose a summand open containing it. An affine open contained in this summand open factors through the original summand inclusion by the open immersion property. Pullback preserves the given inclusion along that factorization. Evaluation on the affine open gives an inclusion of the original ideals there. The local criterion for inclusion now gives the global inequality.
-/
theorem le_of_comap_summandι_le (D : FiniteOpenCoverWithIdeals T) {J J' : D.disjointUnion.IdealSheafData}
    (h : ∀ i : D.idx, J.comap (D.summandι i) ≤ J'.comap (D.summandι i)) : J ≤ J' := by
  classical
  choose idxf hidxf using D.exists_mem_summandOpen
  refine le_of_ideal_le_locally (fun y => D.summandOpen (idxf y)) hidxf ?_
  intro y W hW hWle
  refine ideal_le_of_comap_ι_le W hW ?_
  have hrange : Set.range W.ι.base ⊆ Set.range (D.summandι (idxf y)).base := by
    rw [Scheme.Opens.range_ι, range_summandι D (idxf y), Scheme.Opens.range_ι]
    exact hWle
  have hg : IsOpenImmersion.lift (D.summandι (idxf y)) W.ι hrange ≫ D.summandι (idxf y)
      = W.ι :=
    IsOpenImmersion.lift_fac (D.summandι (idxf y)) W.ι hrange
  have e1 : J.comap W.ι
      = (J.comap (D.summandι (idxf y))).comap
        (IsOpenImmersion.lift (D.summandι (idxf y)) W.ι hrange) := by
    rw [← Scheme.IdealSheafData.comap_comp, hg]
  have e2 : J'.comap W.ι
      = (J'.comap (D.summandι (idxf y))).comap
        (IsOpenImmersion.lift (D.summandι (idxf y)) W.ι hrange) := by
    rw [← Scheme.IdealSheafData.comap_comp, hg]
  rw [e1, e2]
  exact Scheme.IdealSheafData.comap_mono _ (h (idxf y))

/- English proof (authored)
On each open summand the total map is the original open inclusion, which is étale. Étaleness is local on the source, and the summands cover the disjoint union.
-/
theorem etale_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) : Etale D.disjointUnionMap :=
  etale_sigmaOpensDesc T.scheme D.opens

instance instEtaleTotalMap (D : FiniteOpenCoverWithIdeals T) : Etale D.disjointUnionMap :=
  etale_disjointUnionMap D

/- English proof (authored)
The disjoint union map is étale. Every étale morphism is smooth.
-/
theorem smooth_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) : Smooth D.disjointUnionMap := by
  have het : Etale D.disjointUnionMap := etale_disjointUnionMap D
  infer_instance

instance instSmoothTotalMap (D : FiniteOpenCoverWithIdeals T) : Smooth D.disjointUnionMap :=
  smooth_disjointUnionMap D

/- English proof (authored)
The disjoint union map is étale and hence smooth. Smooth morphisms are flat.
-/
theorem flat_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) : Flat D.disjointUnionMap := by
  have he : Etale D.disjointUnionMap := etale_disjointUnionMap D
  have hs : Smooth D.disjointUnionMap := inferInstance
  infer_instance

/- English proof (authored)
On the open summands the map is the inclusion of an open, which is locally of finite type. These summands cover the source, so the total map is locally of finite type.
-/
theorem locallyOfFiniteType_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) : LocallyOfFiniteType D.disjointUnionMap :=
  locallyOfFiniteType_sigmaOpensDesc T.scheme D.opens

instance instLocallyOfFiniteTypeTotalMap (D : FiniteOpenCoverWithIdeals T) : LocallyOfFiniteType D.disjointUnionMap :=
  locallyOfFiniteType_disjointUnionMap D

/- English proof (authored)
For an arbitrary target point, the open cover assumption puts it in one of the original opens. The corresponding point on that summand maps to the chosen point, proving surjectivity.
-/
theorem surjective_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) (h : iSup D.opens = ⊤) :
    Surjective D.disjointUnionMap :=
  surjective_sigmaOpensDesc T.scheme D.opens h

/- English proof (authored)
Each scheme in the finite coproduct is affine by hypothesis. A finite disjoint union of affine schemes is affine, with coordinate ring the finite product of the section rings.
-/
theorem isAffine_disjointUnion (D : FiniteOpenCoverWithIdeals T) (h : ∀ i : D.idx, IsAffineOpen (D.opens i)) :
    IsAffine D.disjointUnion :=
  isAffine_sigmaOpens T.scheme D.opens h

/- English proof (authored)
A field has only one prime ideal, its zero ideal. Hence its spectrum is a subsingleton.
-/
private theorem subsingleton_spec (k : Type u) [Field k] :
    Subsingleton ↥(Spec (CommRingCat.of k)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

/- English proof (authored)
The finite disjoint union of the affine cover opens is affine and therefore quasi-compact. The spectrum of the base field has one point. The inverse image of an open there is either empty or the whole quasi-compact source, so the composite is quasi-compact.
-/
theorem quasiCompact_disjointUnionMap_comp (D : FiniteOpenCoverWithIdeals T)
    (h : ∀ i : D.idx, IsAffineOpen (D.opens i)) :
    QuasiCompact (D.disjointUnionMap ≫ T.structMap) := by
  have haff : IsAffine D.disjointUnion := isAffine_disjointUnion D h
  have hcs : CompactSpace ↥D.disjointUnion := inferInstance
  have hsub : Subsingleton ↥(Spec (CommRingCat.of T.base)) := subsingleton_spec T.base
  exact AlgebraicGeometry.quasiCompact_of_compactSpace_of_subsingleton
    (D.disjointUnionMap ≫ T.structMap)

/- English proof (authored)
At a point of the total space choose its summand open and transport the given étale chart from that summand. The assembled ideal restricts to the given local ideal under this identification. It is therefore either unit or generated by the chosen single étale coordinate. The local coordinate criterion for a smooth divisor applies.
-/
theorem isSmoothDivisor_iInfImageIdeal_of_exists_etaleChart (D : FiniteOpenCoverWithIdeals T)
    (h : ∀ i : D.idx, ∃ (n : ℕ) (c : EtaleChart T.structMap (D.opens i) n),
      D.localIdeal i = ⊤ ∨ ∃ j : Fin n, D.localIdeal i = c.coordIdeal {j}) :
    IsSmoothDivisor (D.disjointUnionMap ≫ T.structMap) D.iInfImageIdeal := by
  refine FunctorialResolution.EmbeddedResolution.isSmoothDivisor_of_locally_coordIdeal D.iInfImageIdeal ?_
  intro x
  obtain ⟨i, hi⟩ := D.exists_mem_summandOpen x
  obtain ⟨n, c, hc⟩ := h i
  refine ⟨D.summandOpen i, hi, n, D.summandEtaleChart i c, ?_⟩
  rcases hc with htop | ⟨j, hj⟩
  · left
    rw [restrictIdeal_iInfImageIdeal_summandOpen D i, htop]
    simp
  · right
    refine ⟨j, ?_⟩
    rw [restrictIdeal_iInfImageIdeal_summandOpen D i, hj]
    exact (summandEtaleChart_coordIdeal D i c {j}).symm

/- English proof (authored)
On a summand with unit ideal, choose any available étale chart. On a summand with a coordinate ideal, use the chart supplied with that coordinate description. In either case there is a chart in which the local ideal is unit or a single coordinate ideal, so the assembled ideal defines a smooth divisor.
-/
theorem isSmoothDivisor_iInfImageIdeal_of_forall_eq_top_or_coordIdeal (D : FiniteOpenCoverWithIdeals T)
    (halt : ∀ i : D.idx, D.localIdeal i = ⊤ ∨
      ∃ (n : ℕ) (c : EtaleChart T.structMap (D.opens i) n) (j : Fin n),
        D.localIdeal i = c.coordIdeal {j})
    (hchart : ∀ i : D.idx, ∃ n : ℕ, Nonempty (EtaleChart T.structMap (D.opens i) n)) :
    IsSmoothDivisor (D.disjointUnionMap ≫ T.structMap) D.iInfImageIdeal := by
  refine isSmoothDivisor_iInfImageIdeal_of_exists_etaleChart D ?_
  intro i
  rcases halt i with htop | ⟨n, c, j, hj⟩
  · obtain ⟨m, ⟨c⟩⟩ := hchart i
    exact ⟨m, c, Or.inl htop⟩
  · exact ⟨n, c, Or.inr ⟨j, hj⟩⟩

end FiniteOpenCoverWithIdeals

end MaxContactReduction

end FunctorialResolution.EmbeddedResolution

end
