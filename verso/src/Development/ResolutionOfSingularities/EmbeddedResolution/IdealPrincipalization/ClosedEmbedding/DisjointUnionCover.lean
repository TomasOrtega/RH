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

/- English proof (translation)
Use `show IsOpenImmersion (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i)`. Use `infer_instance`.
-/
theorem isOpenImmersion_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsOpenImmersion (D.summandι i) := by
  show IsOpenImmersion (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i)
  infer_instance

instance instIsOpenImmersionSummandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsOpenImmersion (D.summandι i) :=
  isOpenImmersion_summandι D i

/- English proof (translation)
Use `show IsClosedImmersion (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i)`. Use `infer_instance`.
-/
theorem isClosedImmersion_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsClosedImmersion (D.summandι i) := by
  show IsClosedImmersion (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i)
  infer_instance

instance instIsClosedImmersionSummandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsClosedImmersion (D.summandι i) :=
  isClosedImmersion_summandι D i

/- English proof (translation)
Use `show QuasiCompact (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i)`. Use `infer_instance`.
-/
theorem quasiCompact_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    QuasiCompact (D.summandι i) := by
  show QuasiCompact (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i)
  infer_instance

instance instQuasiCompactSummandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    QuasiCompact (D.summandι i) :=
  quasiCompact_summandι D i

/- English proof (translation)
The claim follows from `sigma_ι_sigmaOpensDesc T.scheme D.opens i`.
-/
theorem summandι_comp_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    D.summandι i ≫ D.disjointUnionMap = (D.opens i).ι :=
  sigma_ι_sigmaOpensDesc T.scheme D.opens i

/- English proof (translation)
Establish `hmem : D.disjointUnionMap.base ((D.summandι i).base y) ∈ Set.range (D.opens i).ι.base`. Rewrite using `[← summandι_comp_disjointUnionMap D i]`. Conclude with `⟨y, rfl⟩`. Rewrite `hmem` using `[Scheme.Opens.range_ι]`. Conclude with `hmem`.
-/
theorem disjointUnionMap_summandι_mem (D : FiniteOpenCoverWithIdeals T) (i : D.idx) (y : D.piece i) :
    D.disjointUnionMap.base ((D.summandι i).base y) ∈ D.opens i := by
  have hmem : D.disjointUnionMap.base ((D.summandι i).base y) ∈ Set.range (D.opens i).ι.base := by
    rw [← summandι_comp_disjointUnionMap D i]
    exact ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι] at hmem
  exact hmem

/- English proof (translation)
The claim follows from `FunctorialResolution.EmbeddedResolution.comap_ker_subschemeι_comp (D.localIdeal i) (D.summandι i)`.
-/
private theorem comap_imageIdealSheaf_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    (imageIdealSheaf (D.summandι i) (D.localIdeal i)).comap (D.summandι i) = D.localIdeal i :=
  FunctorialResolution.EmbeddedResolution.comap_ker_subschemeι_comp (D.localIdeal i) (D.summandι i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem imageIdealSheaf_eq_ker {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (I : X.IdealSheafData) : imageIdealSheaf f I = Scheme.Hom.ker (I.subschemeι ≫ f) := rfl

/- English proof (translation)
Establish `ht : CategoryTheory.Limits.IsTerminal (Z.presheaf.obj (Opposite.op (⊥ : Z.Opens)))` using `TopCat.Sheaf.isTerminalOfEmpty Z.sheaf`. Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Establish `h` using `ht.hom_ext (CommRingCat.ofHom (RingHom.fst ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens))) ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens))))) (CommRingCat.ofHom (RingHom.snd ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens))) ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens)))))`. Conclude with `congrArg (fun m => (CommRingCat.Hom.hom m) (a, b)) h`.
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

/- English proof (translation)
Establish `hempty : g ⁻¹ᵁ U.1 = ⊥`. Use `TopologicalSpace.Opens.ext ?_` and prove the remaining obligations. Rewrite using `[TopologicalSpace.Opens.coe_bot]`. Conclude with `Set.eq_empty_iff_forall_notMem.mpr fun z hz => hdisj z hz`. Establish `hsub : Subsingleton ↥(Z.presheaf.obj (Opposite.op (g ⁻¹ᵁ U.1)))`.

Rewrite using `[hempty]`. Conclude with `subsingleton_sections_bot Z`. Rewrite using `[Scheme.Hom.ker_apply]`. Use `(Ideal.eq_top_iff_one _).mpr ?_` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker, map_one]`.

Conclude with `Subsingleton.elim _ _`.
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

/- English proof (translation)
Rewrite using `[imageIdealSheaf_eq_ker]`. Use `ideal_ker_eq_top_of_disjoint ((D.localIdeal j).subschemeι ≫ D.summandι j) ⟨W, hW⟩ ?_` and prove the remaining obligations. Introduce `z hz`. Take `⟨v, hv⟩` from `hsub _ hz`. Establish `hcomp : ((D.localIdeal j).subschemeι ≫ D.summandι j).base z = (D.summandι j).base ((D.localIdeal j).subschemeι.base z)` using `rfl`.

Conclude with `Blowup.sigmaι_base_ne (fun t : D.idx => (D.opens t).toScheme) hij ((D.localIdeal j).subschemeι.base z) v (hcomp.symm.trans hv.symm)`.
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

/- English proof (translation)
Establish `hglue : D.iInfImageIdeal = ⨅ j : D.idx, imageIdealSheaf (D.summandι j) (D.localIdeal j)` using `rfl`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Rewrite using `[hglue]`. Conclude with `le_trans (Scheme.IdealSheafData.comap_mono (D.summandι i) (iInf_le _ i)) (le_of_eq (comap_imageIdealSheaf_summandι D i))`. Rewrite using `[Scheme.IdealSheafData.le_def]`.

Introduce `V`. Establish `hW : IsAffineOpen ((D.summandι i) ''ᵁ V.1)` using `V.2.image_of_isOpenImmersion (D.summandι i)`. Establish `hle : V.1 ≤ (D.summandι i) ⁻¹ᵁ ((D.summandι i) ''ᵁ V.1)` using `fun x hx => ⟨x, hx, rfl⟩`. Establish `hsub : ∀ y ∈ ((((D.summandι i) ''ᵁ V.1) : D.disjointUnion.Opens) : Set ↥D.disjointUnion), y ∈ Set.range (D.summandι i).base`. Introduce and unpack `y ⟨v, hv, rfl⟩`.

Conclude with `⟨v, rfl⟩`. Establish `h1` using `Scheme.IdealSheafData.comap_ideal_eq_map_appLE D.iInfImageIdeal (D.summandι i) ⟨_, hW⟩ V hle`. Establish `h2` using `Scheme.IdealSheafData.comap_ideal_eq_map_appLE (imageIdealSheaf (D.summandι i) (D.localIdeal i)) (D.summandι i) ⟨_, hW⟩ V hle`. Establish `h3 : D.iInfImageIdeal.ideal ⟨_, hW⟩ = (imageIdealSheaf (D.summandι i) (D.localIdeal i)).ideal ⟨_, hW⟩`. Rewrite using `[hglue]`.

Simplify using `only [Scheme.IdealSheafData.ideal_iInf, iInf_apply]`. Use `le_antisymm (iInf_le _ i) (le_iInf fun j => ?_)` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Rewrite using `[hj]`. Rewrite using `[ideal_imageIdealSheaf_eq_top_of_ne D hj _ hW hsub]`.

Conclude with `le_top`. Establish `h4 : (D.iInfImageIdeal.comap (D.summandι i)).ideal V = (D.localIdeal i).ideal V`. Rewrite using `[h1, h3, ← h2, comap_imageIdealSheaf_summandι D i]`. Conclude with `le_of_eq h4.symm`.
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

/- English proof (translation)
The claim follows from `(Scheme.Opens.range_ι (D.summandOpen i)).symm`.
-/
theorem range_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    Set.range (D.summandι i).base = Set.range (D.summandOpen i).ι.base :=
  (Scheme.Opens.range_ι (D.summandOpen i)).symm

abbrev summandIso (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    D.piece i ≅ (D.summandOpen i).toScheme :=
  IsOpenImmersion.isoOfRangeEq (D.summandι i) (D.summandOpen i).ι (range_summandι D i)

/- English proof (translation)
Establish `h : (D.summandIso i).inv ≫ D.summandι i = (D.summandOpen i).ι`. Simplify using `[FiniteOpenCoverWithIdeals.summandIso]`. Rewrite using `[← h, Category.assoc, summandι_comp_disjointUnionMap]`.
-/
theorem summandOpen_ι_comp_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    (D.summandOpen i).ι ≫ D.disjointUnionMap = (D.summandIso i).inv ≫ (D.opens i).ι := by
  have h : (D.summandIso i).inv ≫ D.summandι i = (D.summandOpen i).ι := by
    simp [FiniteOpenCoverWithIdeals.summandIso]
  rw [← h, Category.assoc, summandι_comp_disjointUnionMap]

/- English proof (translation)
Take `⟨⟨i, y⟩, hx⟩` from `(sigmaMk fun j : D.idx => (D.opens j).toScheme).surjective x`. Use `⟨i, y, ?_⟩` and prove the remaining obligations. Use `show (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i).base y = x`. Simplify using `using hx`.
-/
theorem exists_summandι_base_eq (D : FiniteOpenCoverWithIdeals T) (x : ↥D.disjointUnion) :
    ∃ (i : D.idx) (y : D.piece i), (D.summandι i).base y = x := by
  obtain ⟨⟨i, y⟩, hx⟩ := (sigmaMk fun j : D.idx => (D.opens j).toScheme).surjective x
  refine ⟨i, y, ?_⟩
  show (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i).base y = x
  simpa using hx

/- English proof (translation)
Take `⟨i, y, hy⟩` from `D.exists_summandι_base_eq x`. Use `⟨i, ?_⟩` and prove the remaining obligations. Establish `hmem : x ∈ Set.range (D.summandι i).base` using `⟨y, hy⟩`. Conclude with `hmem`.
-/
theorem exists_mem_summandOpen (D : FiniteOpenCoverWithIdeals T) (x : ↥D.disjointUnion) :
    ∃ i : D.idx, x ∈ D.summandOpen i := by
  obtain ⟨i, y, hy⟩ := D.exists_summandι_base_eq x
  refine ⟨i, ?_⟩
  have hmem : x ∈ Set.range (D.summandι i).base := ⟨y, hy⟩
  exact hmem

/- English proof (translation)
Establish `hA : IsAffine ((D.opens i).toScheme)` using `h`. Conclude with `isAffineOpen_opensRange (D.summandι i)`.
-/
theorem isAffineOpen_summandOpen (D : FiniteOpenCoverWithIdeals T) (i : D.idx) (h : IsAffineOpen (D.opens i)) :
    IsAffineOpen (D.summandOpen i) := by
  have hA : IsAffine ((D.opens i).toScheme) := h
  exact isAffineOpen_opensRange (D.summandι i)

/- English proof (translation)
Establish `h : (D.summandIso i).inv ≫ D.summandι i = (D.summandOpen i).ι`. Simplify using `[FiniteOpenCoverWithIdeals.summandIso]`. Rewrite using `[restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp, h]`.
-/
theorem restrictIdeal_summandOpen (D : FiniteOpenCoverWithIdeals T) (i : D.idx) (J : D.disjointUnion.IdealSheafData) :
    restrictIdeal J (D.summandOpen i) = (J.comap (D.summandι i)).comap (D.summandIso i).inv := by
  have h : (D.summandIso i).inv ≫ D.summandι i = (D.summandOpen i).ι := by
    simp [FiniteOpenCoverWithIdeals.summandIso]
  rw [restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp, h]

/- English proof (translation)
Rewrite using `[restrictIdeal_summandOpen D i D.iInfImageIdeal, comap_iInfImageIdeal_summandι D i]`.
-/
theorem restrictIdeal_iInfImageIdeal_summandOpen (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    restrictIdeal D.iInfImageIdeal (D.summandOpen i) =
      (D.localIdeal i).comap (D.summandIso i).inv := by
  rw [restrictIdeal_summandOpen D i D.iInfImageIdeal, comap_iInfImageIdeal_summandι D i]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iInfImageIdeal_eq_iInf (D : FiniteOpenCoverWithIdeals T) :
    D.iInfImageIdeal = ⨅ i : D.idx, imageIdealSheaf (D.summandι i) (D.localIdeal i) :=
  rfl

/- English proof (translation)
Rewrite using `[restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, summandOpen_ι_comp_disjointUnionMap]`.
-/
theorem restrictIdeal_comap_disjointUnionMap_summandOpen (D : FiniteOpenCoverWithIdeals T) (i : D.idx)
    (J : T.scheme.IdealSheafData) :
    restrictIdeal (J.comap D.disjointUnionMap) (D.summandOpen i) =
      (restrictIdeal J (D.opens i)).comap (D.summandIso i).inv := by
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, summandOpen_ι_comp_disjointUnionMap]

/- English proof (translation)
Rewrite using `[Category.assoc, c.comp_struct, ← Category.assoc, ← summandOpen_ι_comp_disjointUnionMap, Category.assoc]`.
-/
private theorem summandIso_inv_comp_map_comp_affineSpaceFinToSpec (D : FiniteOpenCoverWithIdeals T) (i : D.idx) {n : ℕ}
    (c : EtaleChart T.structMap (D.opens i) n) :
    ((D.summandIso i).inv ≫ c.map) ≫ affineSpaceFinToSpec T.base n =
      (D.summandOpen i).ι ≫ (D.disjointUnionMap ≫ T.structMap) := by
  rw [Category.assoc, c.comp_struct, ← Category.assoc, ← summandOpen_ι_comp_disjointUnionMap,
    Category.assoc]

/- English proof (translation)
Establish `h1 : Etale c.map` using `c.isEtale`. Establish `h4 : Etale ((D.summandIso i).inv)` using `inferInstance`. Use `infer_instance`.
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

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem summandEtaleChart_map (D : FiniteOpenCoverWithIdeals T) (i : D.idx) {n : ℕ}
    (c : EtaleChart T.structMap (D.opens i) n) :
    (D.summandEtaleChart i c).map = (D.summandIso i).inv ≫ c.map := rfl

/- English proof (translation)
Rewrite using `[EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, summandEtaleChart_map, ← Scheme.IdealSheafData.comap_comp]`.
-/
theorem summandEtaleChart_coordIdeal (D : FiniteOpenCoverWithIdeals T) (i : D.idx) {n : ℕ}
    (c : EtaleChart T.structMap (D.opens i) n) (S : Finset (Fin n)) :
    (D.summandEtaleChart i c).coordIdeal S = (c.coordIdeal S).comap (D.summandIso i).inv := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, summandEtaleChart_map,
    ← Scheme.IdealSheafData.comap_comp]

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hmem : φ x ∈ Ideal.map φ I'`. Rewrite using `[← h]`.

Conclude with `Ideal.mem_map_of_mem φ hx`. Take `⟨a, ha, hax⟩` from `(Ideal.mem_map_iff_of_surjective (f := φ) hsurj).mp hmem`. Establish `hax' : a = x` using `hinj hax`. Rewrite `ha` using `[hax']`. Conclude with `ha`.

Introduce `hx`. Establish `hmem : φ x ∈ Ideal.map φ I`. Rewrite using `[h]`. Conclude with `Ideal.mem_map_of_mem φ hx`. Take `⟨a, ha, hax⟩` from `(Ideal.mem_map_iff_of_surjective (f := φ) hsurj).mp hmem`.

Establish `hax' : a = x` using `hinj hax`. Rewrite `ha` using `[hax']`. Conclude with `ha`.
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

/- English proof (translation)
Introduce `y _`. Conclude with `y.2`.
-/
private theorem top_le_preimage_opens {X : Scheme.{u}} (V : X.Opens) :
    (⊤ : V.toScheme.Opens) ≤ (TopologicalSpace.Opens.map V.ι.base).obj V := by
  intro y _
  exact y.2

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
private theorem appLE_ι_eq_topIso_inv {X : Scheme.{u}} (V : X.Opens) :
    V.ι.appLE V ⊤ (top_le_preimage_opens V) = V.topIso.inv := by
  simp
  rfl

/- English proof (translation)
Establish `: IsAffine V.toScheme` using `hV`. Establish `key1` using `Scheme.IdealSheafData.comap_ideal_eq_map_appLE I V.ι ⟨V, hV⟩ ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_preimage_opens V)`. Establish `key2` using `Scheme.IdealSheafData.comap_ideal_eq_map_appLE J V.ι ⟨V, hV⟩ ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_preimage_opens V)`. Rewrite `key1` using `[h]`. Establish `hinj : Function.Injective (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_preimage_opens V)))`.

Rewrite using `[appLE_ι_eq_topIso_inv V]`. Conclude with `V.topIso.symm.commRingCatIsoToRingEquiv.injective`. Establish `hsurj : Function.Surjective (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_preimage_opens V)))`. Rewrite using `[appLE_ι_eq_topIso_inv V]`. Conclude with `V.topIso.symm.commRingCatIsoToRingEquiv.surjective`.

Conclude with `eq_of_map_eq_of_bijective _ hinj hsurj (key1.symm.trans key2)`.
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

/- English proof (translation)
Use `Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := {W : X.affineOpens // ∃ i : ι, (W.1 : X.Opens) ≤ U i}) (fun W => W.1) ?_ ?_` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx : x ∈ iSup U`. Rewrite using `[hU]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.mp hx`. Take `⟨V, hV, hxV, hVU⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hi`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, i, hVU⟩, hxV⟩`. Introduce and unpack `⟨⟨W, hW⟩, i, hWU⟩`.

Use `ideal_eq_of_comap_ι_eq W hW ?_` and prove the remaining obligations. Establish `e1 : I.comap W.ι = (I.comap (U i).ι).comap (X.homOfLE hWU)`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]`. Establish `e2 : J.comap W.ι = (J.comap (U i).ι).comap (X.homOfLE hWU)`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]`.

Rewrite using `[e1, e2, h i]`.
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

/- English proof (translation)
Use `ext_of_comap_ι_eq_of_iSup_eq_top (fun i : D.idx => D.summandOpen i) ?_ ?_` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨i, hi⟩` from `D.exists_mem_summandOpen x`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩`.

Introduce `i`. Establish `h1` using `restrictIdeal_summandOpen D i J`. Establish `h2` using `restrictIdeal_summandOpen D i J'`. Rewrite `h1` using `[h i]`. Conclude with `h1.trans h2.symm`.
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

/- English proof (translation)
Introduce `a ha`. Establish `h1 : φ a ∈ Ideal.map φ I'` using `h (Ideal.mem_map_of_mem φ ha)`. Take `⟨b, hb, hba⟩` from `(Ideal.mem_map_iff_of_surjective (f := φ) hsurj).mp h1`. Establish `hba' : b = a` using `hinj hba`. Rewrite `hb` using `[hba']`. Then use the resulting hypothesis.
-/
private theorem ideal_le_of_map_le_of_bijective {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hinj : Function.Injective φ) (hsurj : Function.Surjective φ)
    {I I' : Ideal A} (h : Ideal.map φ I ≤ Ideal.map φ I') : I ≤ I' := by
  intro a ha
  have h1 : φ a ∈ Ideal.map φ I' := h (Ideal.mem_map_of_mem φ ha)
  obtain ⟨b, hb, hba⟩ := (Ideal.mem_map_iff_of_surjective (f := φ) hsurj).mp h1
  have hba' : b = a := hinj hba
  rwa [hba'] at hb

/- English proof (translation)
Establish `: IsAffine V.toScheme` using `hV`. Establish `k1` using `Scheme.IdealSheafData.comap_ideal_eq_map_appLE J V.ι ⟨V, hV⟩ ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_preimage_opens V)`. Establish `k2` using `Scheme.IdealSheafData.comap_ideal_eq_map_appLE J' V.ι ⟨V, hV⟩ ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_preimage_opens V)`. Establish `hle` using `Scheme.IdealSheafData.le_def.mp h ⟨⊤, isAffineOpen_top V.toScheme⟩`. Rewrite `hle` using `[k1, k2, appLE_ι_eq_topIso_inv V]`.

Establish `hinj : Function.Injective (CommRingCat.Hom.hom V.topIso.inv)` using `V.topIso.symm.commRingCatIsoToRingEquiv.injective`. Establish `hsurj : Function.Surjective (CommRingCat.Hom.hom V.topIso.inv)` using `V.topIso.symm.commRingCatIsoToRingEquiv.surjective`. Conclude with `ideal_le_of_map_le_of_bijective _ hinj hsurj hle`.
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

/- English proof (translation)
Establish `key : J ⊓ J' = J`. Use `Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := {W : Y.affineOpens // ∃ y : ↥Y, (W.1 : Y.Opens) ≤ V y}) (fun W => W.1) ?_ ?_` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨W, hW, hxW, hWV⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (hmem x)`.

Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, x, hWV⟩, hxW⟩`. Introduce and unpack `⟨⟨W, hW⟩, y, hWV⟩ show (J ⊓ J').ideal ⟨W, hW⟩ = J.ideal ⟨W, hW⟩`. Simplify using `only [Scheme.IdealSheafData.ideal_inf, Pi.inf_apply, inf_eq_left]`. Conclude with `hloc y W hW hWV`. Conclude with `inf_eq_left.mp key`.
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

/- English proof (translation)
Use `choose idxf hidxf using D.exists_mem_summandOpen`. Use `le_of_ideal_le_locally (fun y => D.summandOpen (idxf y)) hidxf ?_` and prove the remaining obligations. Introduce `y W hW hWle`. Use `ideal_le_of_comap_ι_le W hW ?_` and prove the remaining obligations. Establish `hrange : Set.range W.ι.base ⊆ Set.range (D.summandι (idxf y)).base`.

Rewrite using `[Scheme.Opens.range_ι, range_summandι D (idxf y), Scheme.Opens.range_ι]`. Conclude with `hWle`. Establish `hg : IsOpenImmersion.lift (D.summandι (idxf y)) W.ι hrange ≫ D.summandι (idxf y) = W.ι` using `IsOpenImmersion.lift_fac (D.summandι (idxf y)) W.ι hrange`. Establish `e1 : J.comap W.ι = (J.comap (D.summandι (idxf y))).comap (IsOpenImmersion.lift (D.summandι (idxf y)) W.ι hrange)`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, hg]`.

Establish `e2 : J'.comap W.ι = (J'.comap (D.summandι (idxf y))).comap (IsOpenImmersion.lift (D.summandι (idxf y)) W.ι hrange)`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, hg]`. Rewrite using `[e1, e2]`. Conclude with `Scheme.IdealSheafData.comap_mono _ (h (idxf y))`.
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

/- English proof (translation)
The claim follows from `etale_sigmaOpensDesc T.scheme D.opens`.
-/
theorem etale_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) : Etale D.disjointUnionMap :=
  etale_sigmaOpensDesc T.scheme D.opens

instance instEtaleTotalMap (D : FiniteOpenCoverWithIdeals T) : Etale D.disjointUnionMap :=
  etale_disjointUnionMap D

/- English proof (translation)
Establish `het : Etale D.disjointUnionMap` using `etale_disjointUnionMap D`. Use `infer_instance`.
-/
theorem smooth_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) : Smooth D.disjointUnionMap := by
  have het : Etale D.disjointUnionMap := etale_disjointUnionMap D
  infer_instance

instance instSmoothTotalMap (D : FiniteOpenCoverWithIdeals T) : Smooth D.disjointUnionMap :=
  smooth_disjointUnionMap D

/- English proof (translation)
Establish `he : Etale D.disjointUnionMap` using `etale_disjointUnionMap D`. Establish `hs : Smooth D.disjointUnionMap` using `inferInstance`. Use `infer_instance`.
-/
theorem flat_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) : Flat D.disjointUnionMap := by
  have he : Etale D.disjointUnionMap := etale_disjointUnionMap D
  have hs : Smooth D.disjointUnionMap := inferInstance
  infer_instance

/- English proof (translation)
The claim follows from `locallyOfFiniteType_sigmaOpensDesc T.scheme D.opens`.
-/
theorem locallyOfFiniteType_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) : LocallyOfFiniteType D.disjointUnionMap :=
  locallyOfFiniteType_sigmaOpensDesc T.scheme D.opens

instance instLocallyOfFiniteTypeTotalMap (D : FiniteOpenCoverWithIdeals T) : LocallyOfFiniteType D.disjointUnionMap :=
  locallyOfFiniteType_disjointUnionMap D

/- English proof (translation)
The claim follows from `surjective_sigmaOpensDesc T.scheme D.opens h`.
-/
theorem surjective_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) (h : iSup D.opens = ⊤) :
    Surjective D.disjointUnionMap :=
  surjective_sigmaOpensDesc T.scheme D.opens h

/- English proof (translation)
The claim follows from `isAffine_sigmaOpens T.scheme D.opens h`.
-/
theorem isAffine_disjointUnion (D : FiniteOpenCoverWithIdeals T) (h : ∀ i : D.idx, IsAffineOpen (D.opens i)) :
    IsAffine D.disjointUnion :=
  isAffine_sigmaOpens T.scheme D.opens h

/- English proof (translation)
The claim follows from `inferInstanceAs (Subsingleton (PrimeSpectrum k))`.
-/
private theorem subsingleton_spec (k : Type u) [Field k] :
    Subsingleton ↥(Spec (CommRingCat.of k)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

/- English proof (translation)
Establish `haff : IsAffine D.disjointUnion` using `isAffine_disjointUnion D h`. Establish `hcs : CompactSpace ↥D.disjointUnion` using `inferInstance`. Establish `hsub : Subsingleton ↥(Spec (CommRingCat.of T.base))` using `subsingleton_spec T.base`. Conclude with `AlgebraicGeometry.quasiCompact_of_compactSpace_of_subsingleton (D.disjointUnionMap ≫ T.structMap)`.
-/
theorem quasiCompact_disjointUnionMap_comp (D : FiniteOpenCoverWithIdeals T)
    (h : ∀ i : D.idx, IsAffineOpen (D.opens i)) :
    QuasiCompact (D.disjointUnionMap ≫ T.structMap) := by
  have haff : IsAffine D.disjointUnion := isAffine_disjointUnion D h
  have hcs : CompactSpace ↥D.disjointUnion := inferInstance
  have hsub : Subsingleton ↥(Spec (CommRingCat.of T.base)) := subsingleton_spec T.base
  exact AlgebraicGeometry.quasiCompact_of_compactSpace_of_subsingleton
    (D.disjointUnionMap ≫ T.structMap)

/- English proof (translation)
Use `FunctorialResolution.EmbeddedResolution.isSmoothDivisor_of_locally_coordIdeal D.iInfImageIdeal ?_` and prove the remaining obligations. Introduce `x`. Take `⟨i, hi⟩` from `D.exists_mem_summandOpen x`. Take `⟨n, c, hc⟩` from `h i`. Use `⟨D.summandOpen i, hi, n, D.summandEtaleChart i c, ?_⟩` and prove the remaining obligations.

Break down `hc with htop | ⟨j, hj⟩` into its components or cases. Use `left`. Rewrite using `[restrictIdeal_iInfImageIdeal_summandOpen D i, htop]`. Simplify using the standard rewrite rules. Use `right`.

Use `⟨j, ?_⟩` and prove the remaining obligations. Rewrite using `[restrictIdeal_iInfImageIdeal_summandOpen D i, hj]`. Conclude with `(summandEtaleChart_coordIdeal D i c {j}).symm`.
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

/- English proof (translation)
Use `isSmoothDivisor_iInfImageIdeal_of_exists_etaleChart D ?_` and prove the remaining obligations. Introduce `i`. Break down `halt i with htop | ⟨n, c, j, hj⟩` into its components or cases. Take `⟨m, ⟨c⟩⟩` from `hchart i`. Conclude with `⟨m, c, Or.inl htop⟩`.

Conclude with `⟨n, c, Or.inr ⟨j, hj⟩⟩`.
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
