import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.ClopenSubscheme
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientCenterImage
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
Every point of the closed subscheme defined by Z maps into the given open, so the inverse image open in that subscheme is the whole subscheme. Its open inclusion is therefore an isomorphism. Restricting Z to the open and taking its image back in the ambient scheme gives the kernel of the composite from this inverse image open. Precomposition by the open isomorphism preserves the kernel, so this is the original defining ideal Z.
-/
theorem imageIdealSheaf_comap_ι_eq_self_of_support_subset {Y : Scheme.{u}} (Z : Y.IdealSheafData)
    (U : Y.Opens) (_hU : IsClosed (U : Set Y))
    (hZ : (Z.support : Set Y) ⊆ (U : Set Y)) :
    imageIdealSheaf U.ι (Z.comap U.ι) = Z := by
  have hmem : ∀ x : ↥Z.subscheme, x ∈ (Z.subschemeι ⁻¹ᵁ U) := by
    intro x
    have hx : Z.subschemeι.base x ∈ (Z.support : Set Y) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact Set.mem_range_self x
    exact hZ hx
  have key : ∀ y : ↥Z.subscheme,
      y ∈ Set.range ⇑(Scheme.Opens.ι (Z.subschemeι ⁻¹ᵁ U)).base := by
    intro y
    rw [Scheme.Opens.range_ι]
    exact hmem y
  obtain ⟨e, he⟩ : ∃ e : Z.subscheme ⟶ (Z.subschemeι ⁻¹ᵁ U).toScheme,
      e ≫ Scheme.Opens.ι (Z.subschemeι ⁻¹ᵁ U) = 𝟙 Z.subscheme := by
    refine ⟨IsOpenImmersion.lift (Scheme.Opens.ι (Z.subschemeι ⁻¹ᵁ U)) (𝟙 Z.subscheme)
      (fun y _ => key y), ?_⟩
    exact IsOpenImmersion.lift_fac ..
  have h2 : Scheme.Opens.ι (Z.subschemeι ⁻¹ᵁ U) ≫ e = 𝟙 (Z.subschemeι ⁻¹ᵁ U).toScheme := by
    rw [← cancel_mono (Scheme.Opens.ι (Z.subschemeι ⁻¹ᵁ U)), Category.assoc, he,
      Category.comp_id, Category.id_comp]
  have : IsIso (Scheme.Opens.ι (Z.subschemeι ⁻¹ᵁ U)) := ⟨⟨e, h2, he⟩⟩
  rw [imageIdealSheaf_eq_ker_subschemeι_comp, ← ker_ι_preimage_comp_subschemeι_eq_ker_comap Z U,
    ker_eq_ker_of_isIso_comp (Scheme.Opens.ι (Z.subschemeι ⁻¹ᵁ U) ≫ Z.subschemeι) Z.subschemeι
      (Scheme.Opens.ι (Z.subschemeι ⁻¹ᵁ U)) rfl,
    Scheme.IdealSheafData.ker_subschemeι]

/- English proof (authored)
On an underlying point the composite first applies the point map of the first morphism and then that of the second. This is the stated equality of functions.
-/
private theorem coe_base_comp {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    ⇑(a ≫ b).base = ⇑b.base ∘ ⇑a.base := by
  funext x
  simp

/- English proof (authored)
The open inclusion is a topological embedding onto the given subset, which is closed by hypothesis. It is therefore a closed embedding. The second map is also a closed embedding, so the composite is one.
-/
private theorem isClosedEmbedding_base_opens_ι_comp_of_isClosed {S Y : Scheme.{u}} (f : S ⟶ Y)
    [IsClosedImmersion f] (U : S.Opens) (hU : IsClosed (U : Set S)) :
    Topology.IsClosedEmbedding ⇑(U.ι ≫ f).base := by
  have hUce : Topology.IsClosedEmbedding ⇑U.ι.base := by
    refine ⟨U.ι.isOpenEmbedding.toIsEmbedding, ?_⟩
    rw [Scheme.Opens.range_ι]
    exact hU
  rw [coe_base_comp]
  exact (Scheme.Hom.isClosedEmbedding f).comp hUce

/- English proof (authored)
The composite of the clopen inclusion and the closed immersion is a closed embedding on points and is quasi-compact. Its kernel support is the closure of its image. The image is the closed image of the given open subset under f, so its closure is itself.
-/
theorem support_ker_opens_ι_comp {S Y : Scheme.{u}} (f : S ⟶ Y) [IsClosedImmersion f]
    (U : S.Opens) (hU : IsClosed (U : Set S)) :
    ((Scheme.Hom.ker (U.ι ≫ f)).support : Set Y) = ⇑f.base '' (U : Set S) := by
  have hce : Topology.IsClosedEmbedding ⇑(U.ι ≫ f).base :=
    isClosedEmbedding_base_opens_ι_comp_of_isClosed f U hU
  have : QuasiCompact (U.ι ≫ f) := by
    constructor
    intro V _ hV
    exact hce.isCompact_preimage hV
  have hrange : Set.range ⇑(U.ι ≫ f).base = ⇑f.base '' (U : Set S) := by
    rw [coe_base_comp, Set.range_comp, Scheme.Opens.range_ι]
  have hclosed : IsClosed (⇑f.base '' (U : Set S)) := by
    rw [← hrange]
    exact hce.isClosed_range
  rw [Scheme.Hom.support_ker, hrange]
  exact hclosed.closure_eq

/- English proof (authored)
The underlying point map of the composite is the composite of the two underlying functions. Its range is the image of the range of the first function under the second.
-/
private theorem range_base_comp {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    Set.range ⇑(a ≫ b).base = ⇑b.base '' Set.range ⇑a.base := by
  rw [coe_base_comp, Set.range_comp]

/- English proof (authored)
A closed embedding identifies the inverse image of a quasi-compact open with its intersection with the closed image. That intersection is closed in the quasi-compact open and is quasi-compact. This gives quasi-compactness of the morphism.
-/
private theorem quasiCompact_of_isClosedEmbedding_base {A B : Scheme.{u}} (g : A ⟶ B)
    (hg : Topology.IsClosedEmbedding ⇑g.base) : QuasiCompact g := by
  constructor
  intro V _ hV
  exact hg.isCompact_preimage hV

/- English proof (authored)
The composite inclusion has image the intersection of U with the inverse image of W under f. That inverse image is contained in U by hypothesis, so the intersection equals the full inverse image. This is the range of its own inclusion.
-/
private theorem range_base_preimage_ι_comp_ι_eq_of_le {S Y : Scheme.{u}} (f : S ⟶ Y) (U : S.Opens)
    (W : Y.Opens) (hW : (f ⁻¹ᵁ W : S.Opens) ≤ U) :
    Set.range ⇑(Scheme.Opens.ι ((U.ι ≫ f) ⁻¹ᵁ W) ≫ U.ι).base
      = Set.range ⇑(Scheme.Opens.ι (f ⁻¹ᵁ W)).base := by
  have h2 : (((U.ι ≫ f) ⁻¹ᵁ W : U.toScheme.Opens) : Set U.toScheme)
      = ⇑U.ι.base ⁻¹' ((f ⁻¹ᵁ W : S.Opens) : Set S) := rfl
  rw [range_base_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι, h2,
    Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
  refine Set.inter_eq_left.mpr ?_
  intro x hx
  exact hW hx

/- English proof (authored)
The hypothesis gives equal images in the original source for the inverse-image open of W under f and the inverse-image open under its restriction to U. Both are open immersions into the original source, so their domains are canonically isomorphic over it. The induced maps to W coincide under that isomorphism, since their composites with the open inclusion agree. The restrictions of the kernel ideals are the kernels of these two maps, which agree under precomposition by the isomorphism.
-/
theorem restrictIdeal_ker_opens_ι_comp_of_preimage_le {S Y : Scheme.{u}} (f : S ⟶ Y) [IsClosedImmersion f]
    (U : S.Opens) (hU : IsClosed (U : Set S)) (W : Y.Opens)
    (hW : (f ⁻¹ᵁ W : S.Opens) ≤ U) :
    restrictIdeal (Scheme.Hom.ker (U.ι ≫ f)) W = restrictIdeal (Scheme.Hom.ker f) W := by
  have hcif : Topology.IsClosedEmbedding ⇑f.base := Scheme.Hom.isClosedEmbedding f
  have _hciU : IsClosedImmersion U.ι :=
    AlgebraicGeometry.Scheme.Opens.isClosedImmersion_ι_of_isClosed U hU
  have _hqf : QuasiCompact f := quasiCompact_of_isClosedEmbedding_base f hcif
  have _hqUf : QuasiCompact (U.ι ≫ f) := by
    refine quasiCompact_of_isClosedEmbedding_base _ ?_
    rw [coe_base_comp]
    exact hcif.comp (Scheme.Hom.isClosedEmbedding U.ι)
  have hrange : Set.range ⇑(Scheme.Opens.ι (f ⁻¹ᵁ W)).base
      = Set.range ⇑(Scheme.Opens.ι ((U.ι ≫ f) ⁻¹ᵁ W) ≫ U.ι).base :=
    (range_base_preimage_ι_comp_ι_eq_of_le f U W hW).symm
  have hfac : ∀ e : (f ⁻¹ᵁ W).toScheme ⟶ ((U.ι ≫ f) ⁻¹ᵁ W).toScheme,
      e ≫ Scheme.Opens.ι ((U.ι ≫ f) ⁻¹ᵁ W) ≫ U.ι = Scheme.Opens.ι (f ⁻¹ᵁ W) →
      e ≫ ((U.ι ≫ f) ∣_ W) = f ∣_ W := by
    intro e he
    have he' : (e ≫ Scheme.Opens.ι ((U.ι ≫ f) ⁻¹ᵁ W)) ≫ U.ι = Scheme.Opens.ι (f ⁻¹ᵁ W) := by
      rw [Category.assoc]
      exact he
    rw [← cancel_mono (Scheme.Opens.ι W), Category.assoc, morphismRestrict_ι,
      morphismRestrict_ι, ← Category.assoc, ← Category.assoc, he']
  have key : (IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι (f ⁻¹ᵁ W))
      (Scheme.Opens.ι ((U.ι ≫ f) ⁻¹ᵁ W) ≫ U.ι) hrange).hom ≫ ((U.ι ≫ f) ∣_ W) = f ∣_ W :=
    hfac _ (IsOpenImmersion.isoOfRangeEq_hom_fac ..)
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ker_comap_ι_eq_ker_morphismRestrict (U.ι ≫ f) W,
    ker_comap_ι_eq_ker_morphismRestrict f W]
  exact (ker_eq_ker_of_isIso_comp (f ∣_ W) ((U.ι ≫ f) ∣_ W)
    (IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι (f ⁻¹ᵁ W))
      (Scheme.Opens.ι ((U.ι ≫ f) ⁻¹ᵁ W) ≫ U.ι) hrange).hom key).symm

/- English proof (authored)
Restricting a strict transform to the inverse image of W computes the strict transform of the restrictions along the restricted morphism. The center is the same in both computations and the two restricted input ideals agree by hypothesis. Their strict transforms therefore agree on this open.
-/
theorem restrictIdeal_strictTransform_congr {Y Y₁ : Scheme.{u}} [IsLocallyNoetherian Y₁]
    (f : Y₁ ⟶ Y) (Z : Y.IdealSheafData) (W : Y.Opens) (A B : Y.IdealSheafData)
    (h : restrictIdeal A W = restrictIdeal B W) :
    restrictIdeal (Blowup.strictTransform f Z A) (f ⁻¹ᵁ W)
      = restrictIdeal (Blowup.strictTransform f Z B) (f ⁻¹ᵁ W) := by
  have hcomp : Scheme.Opens.ι (f ⁻¹ᵁ W) ≫ f = (f ∣_ W) ≫ Scheme.Opens.ι W :=
    (morphismRestrict_ι f W).symm
  have hA : restrictIdeal (Blowup.strictTransform f Z A) (f ⁻¹ᵁ W)
      = Blowup.strictTransform (f ∣_ W) (restrictIdeal Z W) (restrictIdeal A W) := by
    rw [restrictIdeal_strictTransform f Z A (f ⁻¹ᵁ W), hcomp,
      strictTransform_comp_ι W (f ∣_ W) Z A]
  have hB : restrictIdeal (Blowup.strictTransform f Z B) (f ⁻¹ᵁ W)
      = Blowup.strictTransform (f ∣_ W) (restrictIdeal Z W) (restrictIdeal B W) := by
    rw [restrictIdeal_strictTransform f Z B (f ⁻¹ᵁ W), hcomp,
      strictTransform_comp_ι W (f ∣_ W) Z B]
  rw [hA, hB, h]

/- English proof (authored)
The inverse images of the two given opens cover the new ambient scheme. On the first, commutativity makes the inverse image along the new immersion lie entirely in the selected lower open. There the kernel of the selected inclusion equals the full embedding kernel, both before and after the transformation. Apply the full strict-transform equality and the locality of strict transform. On the second open the selected original image is empty by hypothesis, and the selected new image is also disjoint by commutativity. The restricted kernels are unit there, and the transform of the unit ideal is unit. The two local equalities prove the global equality.
-/
private theorem ker_preimage_ι_comp_eq_strictTransform_of_cover {S Y S₁ Y₁ : Scheme.{u}}
    [IsLocallyNoetherian Y₁]
    (ι : S ⟶ Y) [IsClosedImmersion ι] (ι₁ : S₁ ⟶ Y₁) [IsClosedImmersion ι₁]
    (g : S₁ ⟶ S) (f : Y₁ ⟶ Y) (hsq : ι₁ ≫ f = g ≫ ι)
    (Z : Y.IdealSheafData) (U : S.Opens) (hU : IsClosed (U : Set S))
    (hU₁ : IsClosed ((g ⁻¹ᵁ U : S₁.Opens) : Set S₁))
    (hker : Scheme.Hom.ker ι₁ = Blowup.strictTransform f Z (Scheme.Hom.ker ι))
    (W₁ W₂ : Y.Opens) (hcov : ∀ y : Y, y ∈ W₁ ∨ y ∈ W₂)
    (h₁ : (ι ⁻¹ᵁ W₁ : S.Opens) ≤ U)
    (h₂ : ∀ x : S, x ∈ U → ι.base x ∉ W₂) :
    Scheme.Hom.ker ((g ⁻¹ᵁ U).ι ≫ ι₁)
      = Blowup.strictTransform f Z (Scheme.Hom.ker (U.ι ≫ ι)) := by
  have hbase : ∀ x : S₁, f.base (ι₁.base x) = ι.base (g.base x) := by
    intro x
    have hh1 : (ι₁ ≫ f).base x = f.base (ι₁.base x) := by simp
    have hh2 : (g ≫ ι).base x = ι.base (g.base x) := by simp
    rw [← hh1, ← hh2, hsq]
  have hpre₁ : (ι₁ ⁻¹ᵁ (f ⁻¹ᵁ W₁) : S₁.Opens) ≤ (g ⁻¹ᵁ U : S₁.Opens) := by
    intro x hx
    have hx' : f.base (ι₁.base x) ∈ W₁ := hx
    rw [hbase x] at hx'
    have hmem : g.base x ∈ (ι ⁻¹ᵁ W₁ : S.Opens) := hx'
    exact h₁ hmem
  refine eq_of_restrictIdeal_eq_of_iSup_eq_top _ _
    (fun b : Bool => cond b (f ⁻¹ᵁ W₁) (f ⁻¹ᵁ W₂)) ?_ ?_
  · rw [eq_top_iff]
    intro y _
    refine TopologicalSpace.Opens.mem_iSup.mpr ?_
    rcases hcov (f.base y) with hy | hy
    · exact ⟨true, hy⟩
    · exact ⟨false, hy⟩
  · intro b
    cases b with
    | false =>
      show restrictIdeal (Scheme.Hom.ker ((g ⁻¹ᵁ U).ι ≫ ι₁)) (f ⁻¹ᵁ W₂)
        = restrictIdeal (Blowup.strictTransform f Z (Scheme.Hom.ker (U.ι ≫ ι))) (f ⁻¹ᵁ W₂)
      have t1 : restrictIdeal (Scheme.Hom.ker ((g ⁻¹ᵁ U).ι ≫ ι₁)) (f ⁻¹ᵁ W₂) = ⊤ := by
        refine (restrictIdeal_eq_top_iff_forall_notMem_support _ _).mpr ?_
        intro y hy hmem
        have hmem' : y ∈ ((Scheme.Hom.ker ((g ⁻¹ᵁ U).ι ≫ ι₁)).support : Set ↥Y₁) := hmem
        rw [support_ker_opens_ι_comp ι₁ (g ⁻¹ᵁ U) hU₁] at hmem'
        obtain ⟨x, hxU, rfl⟩ := hmem'
        have hxU' : g.base x ∈ U := hxU
        have hfy : f.base (ι₁.base x) ∈ W₂ := hy
        rw [hbase x] at hfy
        exact h₂ (g.base x) hxU' hfy
      have t2 : restrictIdeal (Scheme.Hom.ker (U.ι ≫ ι)) W₂ = ⊤ := by
        refine (restrictIdeal_eq_top_iff_forall_notMem_support _ _).mpr ?_
        intro y hy hmem
        have hmem' : y ∈ ((Scheme.Hom.ker (U.ι ≫ ι)).support : Set ↥Y) := hmem
        rw [support_ker_opens_ι_comp ι U hU] at hmem'
        obtain ⟨x, hxU, rfl⟩ := hmem'
        have hxU' : x ∈ U := hxU
        exact h₂ x hxU' hy
      have t3 : restrictIdeal (Scheme.Hom.ker (U.ι ≫ ι)) W₂
          = restrictIdeal (⊤ : Y.IdealSheafData) W₂ := by
        rw [t2]
        exact (Scheme.IdealSheafData.comap_top ..).symm
      have htop : Blowup.strictTransform f Z (⊤ : Y.IdealSheafData) = (⊤ : Y₁.IdealSheafData) := by
        refine le_antisymm le_top ?_
        have hle := Blowup.comap_le_strictTransform f Z (⊤ : Y.IdealSheafData)
        rwa [Scheme.IdealSheafData.comap_top] at hle
      rw [t1, restrictIdeal_strictTransform_congr f Z W₂ _ _ t3, htop]
      exact (Scheme.IdealSheafData.comap_top ..).symm
    | true =>
      show restrictIdeal (Scheme.Hom.ker ((g ⁻¹ᵁ U).ι ≫ ι₁)) (f ⁻¹ᵁ W₁)
        = restrictIdeal (Blowup.strictTransform f Z (Scheme.Hom.ker (U.ι ≫ ι))) (f ⁻¹ᵁ W₁)
      have e1 := restrictIdeal_ker_opens_ι_comp_of_preimage_le ι₁ (g ⁻¹ᵁ U) hU₁ (f ⁻¹ᵁ W₁) hpre₁
      have e2 := restrictIdeal_ker_opens_ι_comp_of_preimage_le ι U hU W₁ h₁
      rw [e1, hker, restrictIdeal_strictTransform_congr f Z W₁ _ _ e2]

/- English proof (authored)
The clopen subset and its complement have disjoint closed images in the original ambient scheme under the closed immersion. Their open complements cover the ambient scheme. The complement of the image of the unselected part has inverse image inside U, and the complement of the image of U misses every selected point. The inverse image of U under the lower transition remains clopen. The two-open strict-transform comparison now applies.
-/
theorem ker_preimage_ι_comp_eq_strictTransform_of_isClopen {S Y S₁ Y₁ : Scheme.{u}} [IsLocallyNoetherian Y₁]
    (ι : S ⟶ Y) [IsClosedImmersion ι] (ι₁ : S₁ ⟶ Y₁) [IsClosedImmersion ι₁]
    (g : S₁ ⟶ S) (f : Y₁ ⟶ Y) (hsq : ι₁ ≫ f = g ≫ ι)
    (Z : Y.IdealSheafData) (U : S.Opens) (hU : IsClosed (U : Set S))
    (hker : Scheme.Hom.ker ι₁ = Blowup.strictTransform f Z (Scheme.Hom.ker ι)) :
    Scheme.Hom.ker ((g ⁻¹ᵁ U).ι ≫ ι₁)
      = Blowup.strictTransform f Z (Scheme.Hom.ker (U.ι ≫ ι)) := by
  have hιemb : Topology.IsClosedEmbedding ⇑ι.base := Scheme.Hom.isClosedEmbedding ι
  have hinj : Function.Injective ⇑ι.base := hιemb.toIsEmbedding.injective
  have hVcl : IsClosed ((U : Set S)ᶜ) := isClosed_compl_iff.mpr U.isOpen
  have hUimg : IsClosed (⇑ι.base '' (U : Set S)) := hιemb.isClosedMap _ hU
  have hVimg : IsClosed (⇑ι.base '' ((U : Set S)ᶜ)) := hιemb.isClosedMap _ hVcl
  have hU₁ : IsClosed ((g ⁻¹ᵁ U : S₁.Opens) : Set S₁) :=
    isOpen_compl_iff.mp (g ⁻¹ᵁ (⟨(U : Set S)ᶜ, hU.isOpen_compl⟩ : S.Opens)).isOpen
  refine ker_preimage_ι_comp_eq_strictTransform_of_cover ι ι₁ g f hsq Z U hU hU₁ hker
    ⟨(⇑ι.base '' ((U : Set S)ᶜ))ᶜ, hVimg.isOpen_compl⟩
    ⟨(⇑ι.base '' (U : Set S))ᶜ, hUimg.isOpen_compl⟩ ?_ ?_ ?_
  · intro y
    by_cases hy : y ∈ ⇑ι.base '' (U : Set S)
    · left
      obtain ⟨x, hxU, rfl⟩ := hy
      show ι.base x ∈ (⇑ι.base '' ((U : Set S)ᶜ))ᶜ
      rintro ⟨x', hx'V, hx'⟩
      have hx'U : x' ∈ (U : Set S) := by
        rw [hinj hx']
        exact hxU
      exact absurd hx'U hx'V
    · right
      show y ∈ (⇑ι.base '' (U : Set S))ᶜ
      exact hy
  · intro x hx
    have hx' : ι.base x ∈ (⇑ι.base '' ((U : Set S)ᶜ))ᶜ := hx
    by_contra hxU
    exact absurd (show ι.base x ∈ ⇑ι.base '' ((U : Set S)ᶜ) from ⟨x, hxU, rfl⟩) hx'
  · intro x hxU hmem
    have hmem' : ι.base x ∈ (⇑ι.base '' (U : Set S))ᶜ := hmem
    exact absurd (show ι.base x ∈ ⇑ι.base '' (U : Set S) from ⟨x, hxU, rfl⟩) hmem'

/- English proof (authored)
The exceptional ideal is the pullback of the center. Restricting it is pullback along the inclusion of the inverse-image open. The composite with the original morphism equals the restricted morphism followed by the original open inclusion. Functoriality identifies this with the pullback of the restricted center.
-/
theorem restrictIdeal_exceptionalIdeal {Y Y₁ : Scheme.{u}} (f : Y₁ ⟶ Y)
    (Z : Y.IdealSheafData) (W : Y.Opens) :
    restrictIdeal (Blowup.exceptionalIdeal f Z) (f ⁻¹ᵁ W)
      = Blowup.exceptionalIdeal (f ∣_ W) (restrictIdeal Z W) := by
  show (Z.comap f).comap (Scheme.Opens.ι (f ⁻¹ᵁ W))
      = (Z.comap (Scheme.Opens.ι W)).comap (f ∣_ W)
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    morphismRestrict_ι]

/- English proof (authored)
First restrict the strict transform on the source by composing the morphism with the inverse-image open inclusion. This composite is the restricted morphism followed by the open inclusion of W. The strict-transform rule for composition with that open inclusion replaces the center and input ideal by their restrictions, giving the stated formula.
-/
theorem restrictIdeal_strictTransform_preimage {Y Y₁ : Scheme.{u}} [IsLocallyNoetherian Y₁]
    (f : Y₁ ⟶ Y) (Z D : Y.IdealSheafData) (W : Y.Opens) :
    restrictIdeal (Blowup.strictTransform f Z D) (f ⁻¹ᵁ W)
      = Blowup.strictTransform (f ∣_ W) (restrictIdeal Z W) (restrictIdeal D W) := by
  have hcomp : Scheme.Opens.ι (f ⁻¹ᵁ W) ≫ f = (f ∣_ W) ≫ Scheme.Opens.ι W :=
    (morphismRestrict_ι f W).symm
  rw [restrictIdeal_strictTransform f Z D (f ⁻¹ᵁ W), hcomp,
    strictTransform_comp_ι W (f ∣_ W) Z D]

end FunctorialResolution.EmbeddedResolution
