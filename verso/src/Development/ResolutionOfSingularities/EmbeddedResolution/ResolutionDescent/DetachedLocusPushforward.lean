import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedCenterFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedLocusFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartPushforward
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.VanishingIdealOfComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IdealSheafFlatDescent
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.StrictTransformClosedImmersion
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace ChartPushforward

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  {S S' : EmbeddedBlowupSequence k Y pY}

/- English proof (authored)
The two continuous inverse maps give a homeomorphism. They carry irreducible sets to irreducible sets in both directions. If the image of a component lies in a larger irreducible set, apply the inverse map and use maximality of the component. Applying the forward map gives maximality of the image. The same argument with the maps reversed proves the converse.
-/
private theorem mem_irreducibleComponents_iff_image {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (f : α → β) (g : β → α) (hf : Continuous f) (hg : Continuous g)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) (C : Set α) :
    C ∈ irreducibleComponents α ↔ f '' C ∈ irreducibleComponents β := by
  have hinj : Function.Injective f := by
    intro a b hab
    have h := congrArg g hab
    rwa [hgf, hgf] at h
  have hirrf : ∀ s : Set α, IsIrreducible s → IsIrreducible (f '' s) := fun s hs =>
    hs.image f hf.continuousOn
  have hirrg : ∀ t : Set β, IsIrreducible t → IsIrreducible (g '' t) := fun t ht =>
    ht.image g hg.continuousOn
  have himg : g '' (f '' C) = C := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      rwa [hgf]
    · intro x hx
      exact ⟨f x, ⟨x, hx, rfl⟩, hgf x⟩
  constructor
  · intro hC0
    have hC : IsIrreducible C ∧ ∀ ⦃b : Set α⦄, IsIrreducible b → C ≤ b → b ≤ C := hC0
    show IsIrreducible (f '' C) ∧ ∀ ⦃b : Set β⦄, IsIrreducible b → f '' C ≤ b → b ≤ f '' C
    refine ⟨hirrf C hC.1, ?_⟩
    intro t ht hsub
    have hsub' : f '' C ⊆ t := hsub
    have hCt : C ⊆ g '' t := fun x hx => ⟨f x, hsub' ⟨x, hx, rfl⟩, hgf x⟩
    have hle : g '' t ⊆ C := hC.2 (hirrg t ht) hCt
    intro y hy
    exact ⟨g y, hle ⟨y, hy, rfl⟩, hfg y⟩
  · intro hC0
    have hC : IsIrreducible (f '' C) ∧
        ∀ ⦃b : Set β⦄, IsIrreducible b → f '' C ≤ b → b ≤ f '' C := hC0
    show IsIrreducible C ∧ ∀ ⦃b : Set α⦄, IsIrreducible b → C ≤ b → b ≤ C
    refine ⟨?_, ?_⟩
    · have h1 := hirrg _ hC.1
      rwa [himg] at h1
    · intro t ht hsub
      have hsub' : C ⊆ t := hsub
      have himt : f '' C ⊆ f '' t := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, hsub' hx, rfl⟩
      have hle : f '' t ⊆ f '' C := hC.2 (hirrf t ht) himt
      intro x hx
      obtain ⟨x', hx', hxx⟩ := hle ⟨x, hx, rfl⟩
      have hx'x : x' = x := hinj hxx
      rwa [← hx'x]

/- English proof (authored)
The strict-transform isomorphism carries irreducible components to irreducible components and reflects that condition. The ambient center support upstairs is the image of the support downstairs under the closed stage comparison. The square with the strict-transform inclusions commutes, so a component image contained in the original center maps to one contained in the new center. Conversely, if its image is contained in the new center, injectivity of the ambient stage comparison forces every original point into the original center. Thus the componentwise containment conditions are equivalent.
-/
theorem mem_detachedComponents_iff (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length)
    (C : Set ↥(S.strictTransform i)) :
    C ∈ S.detachedComponents i ↔
      ⇑((P.strictTransformIso i hi.le).hom) '' C ∈ S'.detachedComponents i := by
  have hgf : ∀ x : ↥(S.strictTransform i),
      ((P.strictTransformIso i hi.le).inv).base (((P.strictTransformIso i hi.le).hom).base x) = x := fun x =>
    Scheme.hom_inv_apply (P.strictTransformIso i hi.le) x
  have hfg : ∀ y : ↥(S'.strictTransform i),
      ((P.strictTransformIso i hi.le).hom).base (((P.strictTransformIso i hi.le).inv).base y) = y := fun y =>
    Scheme.inv_hom_apply (P.strictTransformIso i hi.le) y
  have hcomm : ∀ x : ↥(S.strictTransform i),
      (S'.strictTransformι i).base (((P.strictTransformIso i hi.le).hom).base x)
        = (P.levelMap i hi.le).base ((S.strictTransformι i).base x) := fun x =>
    congrArg (fun g : S.strictTransform i ⟶ S'.schemeAt i => g.base x)
      (P.strictTransformIso_hom_comp_strictTransformι i hi.le)
  have hinj :=
    (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding (P.levelMap i hi.le)).injective
  have hsupp := P.support_ambientCenter_eq_image i hi
  simp only [EmbeddedBlowupSequence.mem_detachedComponents]
  refine and_congr (mem_irreducibleComponents_iff_image (⇑((P.strictTransformIso i hi.le).hom))
    (⇑((P.strictTransformIso i hi.le).inv)) (P.strictTransformIso i hi.le).hom.base.hom.continuous
    (P.strictTransformIso i hi.le).inv.base.hom.continuous hgf hfg C) ?_
  constructor
  · intro h z hz
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨x, hxC, rfl⟩ := hy
    rw [hsupp]
    exact ⟨(S.strictTransformι i).base x, h ⟨x, hxC, rfl⟩, (hcomm x).symm⟩
  · intro h z hz
    obtain ⟨x, hxC, rfl⟩ := hz
    have hmem : (S'.strictTransformι i).base (((P.strictTransformIso i hi.le).hom).base x)
        ∈ ((S'.ambientCenter i).support : Set ↥(S'.schemeAt i)) :=
      h ⟨((P.strictTransformIso i hi.le).hom).base x, ⟨x, hxC, rfl⟩, rfl⟩
    rw [hsupp] at hmem
    obtain ⟨w, hw, hweq⟩ := hmem
    have hweq' : (P.levelMap i hi.le).base w
        = (P.levelMap i hi.le).base ((S.strictTransformι i).base x) := hweq.trans (hcomm x)
    have hwx : w = (S.strictTransformι i).base x := hinj hweq'
    rwa [hwx] at hw

/- English proof (authored)
A point of a set in the source family maps into the image of that set, which belongs to the target family. Conversely, for a point of a target family member, choose a preimage by surjectivity. The inverse image of that member maps onto the member and hence belongs to the source family by the assumed equivalence. This preimage point belongs to the source union, proving the reverse containment.
-/
private theorem sUnion_eq_image_sUnion {α β : Type u} (f : α → β)
    (hf : Function.Surjective f) (A : Set (Set α)) (B : Set (Set β))
    (h : ∀ C : Set α, C ∈ A ↔ f '' C ∈ B) :
    ⋃₀ B = f '' (⋃₀ A) := by
  apply Set.Subset.antisymm
  · rintro x ⟨D, hD, hxD⟩
    obtain ⟨y, rfl⟩ := hf x
    refine ⟨y, ⟨f ⁻¹' D, ?_, hxD⟩, rfl⟩
    refine (h (f ⁻¹' D)).mpr ?_
    rw [Set.image_preimage_eq D hf]
    exact hD
  · rintro z ⟨y, hy, rfl⟩
    obtain ⟨C, hC, hyC⟩ := hy
    exact ⟨f '' C, (h C).mp hC, ⟨y, hyC, rfl⟩⟩

/- English proof (authored)
The strict-transform isomorphism is surjective and sends exactly the detached components to the detached components of the target. Taking their unions therefore sends the original detached locus onto the target one.
-/
theorem detachedLocus_eq_image (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    S'.detachedLocus i = ⇑((P.strictTransformIso i hi.le).hom) '' S.detachedLocus i := by
  have hsurj : Function.Surjective ⇑((P.strictTransformIso i hi.le).hom) :=
    (Scheme.homeoOfIso (P.strictTransformIso i hi.le)).surjective
  rw [S'.detachedLocus_eq_sUnion i, S.detachedLocus_eq_sUnion i]
  exact sUnion_eq_image_sUnion _ hsurj _ _
    (fun C => P.mem_detachedComponents_iff i hi C)

/- English proof (authored)
The strict-transform isomorphism gives a homeomorphism on point spaces. It sends the original detached locus to the target locus and commutes with taking topological closure, giving the equality.
-/
theorem coe_detachedClosure_eq_image (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) =
      ⇑((P.strictTransformIso i hi.le).hom) '' (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) := by
  have h1 : (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) = closure (S'.detachedLocus i) := rfl
  have h2 : (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) = closure (S.detachedLocus i) := rfl
  rw [h1, h2, P.detachedLocus_eq_image i hi]
  exact ((Scheme.homeoOfIso (P.strictTransformIso i hi.le)).image_closure (S.detachedLocus i)).symm

/- English proof (authored)
The target detached closure is the image of the original closure. The strict-transform map is injective, so the inverse image of that image is the original closure.
-/
theorem preimage_coe_detachedClosure (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    ⇑((P.strictTransformIso i hi.le).hom) ⁻¹' (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) =
      (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) := by
  rw [P.coe_detachedClosure_eq_image i hi]
  exact Set.preimage_image_eq _ (Scheme.homeoOfIso (P.strictTransformIso i hi.le)).injective

/- English proof (authored)
The strict transforms are reduced and Noetherian. Their isomorphism is flat and takes the inverse image of the target detached closure to the original detached closure. The target closure is a union of irreducible components. The flat pullback formula for the vanishing ideal of such a union identifies its pullback with the original detached ideal.
-/
theorem comap_detachedIdeal (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i < S'.length) :
    (S'.detachedIdeal i).comap (P.strictTransformIso i hi.le).hom = S.detachedIdeal i := by
  have hn' : TopologicalSpace.NoetherianSpace ↥(S'.strictTransform i) :=
    S'.noetherianSpace_strictTransform i hi.le
  have hn : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) :=
    S.noetherianSpace_strictTransform i (P.le_length hi.le)
  have hr' : AlgebraicGeometry.IsReduced (S'.strictTransform i) :=
    S'.isReduced_strictTransform i hi.le
  have hr : AlgebraicGeometry.IsReduced (S.strictTransform i) :=
    S.isReduced_strictTransform i (P.le_length hi.le)
  have hfl : AlgebraicGeometry.Flat (P.strictTransformIso i hi.le).hom := inferInstance
  have hS : S'.detachedComponents i ⊆ irreducibleComponents ↥(S'.strictTransform i) :=
    fun C hC => ((S'.mem_detachedComponents i C).mp hC).1
  have hZ : (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) = ⋃₀ (S'.detachedComponents i) :=
    (S'.detachedClosure_coe i).trans (S'.detachedLocus_eq_sUnion i)
  have hZ' : (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) =
      ⇑((P.strictTransformIso i hi.le).hom).base ⁻¹' (⋃₀ (S'.detachedComponents i)) := by
    rw [← hZ]
    exact (P.preimage_coe_detachedClosure i hi).symm
  rw [S'.detachedIdeal_eq i, S.detachedIdeal_eq i]
  exact comap_vanishingIdeal_sUnion (P.strictTransformIso i hi.le).hom hS hZ hZ'

/- English proof (authored)
The ideal pullback equality lets the forward ambient isomorphism restrict to a map between the two closed subschemes. Pulling the equality back by the inverse gives the restriction in the reverse direction. The composites become identities after composing with the closed immersions, so cancellation makes them inverse. The forward restriction has the desired ambient compatibility.
-/
private theorem exists_subschemeIso_of_comap_eq {X Z : Scheme.{u}} (e : X ≅ Z)
    (I : X.IdealSheafData) (J : Z.IdealSheafData) (h : J.comap e.hom = I) :
    ∃ u : I.subscheme ≅ J.subscheme, u.hom ≫ J.subschemeι = I.subschemeι ≫ e.hom := by
  have h1 : J ≤ I.map e.hom :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr (le_of_eq h)
  have hcomp : I.comap e.inv = J := by
    rw [← h, ← Scheme.IdealSheafData.comap_comp, e.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  have h2 : I ≤ J.map e.inv :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr (le_of_eq hcomp)
  obtain ⟨a, ha⟩ : ∃ a : I.subscheme ⟶ J.subscheme,
      a ≫ J.subschemeι = I.subschemeι ≫ e.hom :=
    ⟨I.subschemeMap J e.hom h1, Scheme.IdealSheafData.subschemeMap_subschemeι I J e.hom h1⟩
  obtain ⟨b, hb⟩ : ∃ b : J.subscheme ⟶ I.subscheme,
      b ≫ I.subschemeι = J.subschemeι ≫ e.inv :=
    ⟨J.subschemeMap I e.inv h2, Scheme.IdealSheafData.subschemeMap_subschemeι J I e.inv h2⟩
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · refine (cancel_mono I.subschemeι).mp ?_
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, e.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · refine (cancel_mono J.subschemeι).mp ?_
    rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc, e.inv_hom_id,
      Category.comp_id, Category.id_comp]

/- English proof (authored)
The strict-transform isomorphism identifies the two detached ideals by pullback. Restrict it to the closed subschemes of these ideals to get an isomorphism commuting with their inclusions.
-/
theorem exists_iso_detachedScheme (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i < S'.length) :
    ∃ e : S.detachedScheme i ≅ S'.detachedScheme i,
      e.hom ≫ S'.detachedι i = S.detachedι i ≫ (P.strictTransformIso i hi.le).hom := by
  exact exists_subschemeIso_of_comap_eq (P.strictTransformIso i hi.le) (S.detachedIdeal i)
    (S'.detachedIdeal i) (P.comap_detachedIdeal i hi)

def detachedSchemeIso (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i < S'.length) : S.detachedScheme i ≅ S'.detachedScheme i :=
  (P.exists_iso_detachedScheme i hi).choose

@[reassoc]
/- English proof (authored)
The detached-scheme isomorphism was chosen with the condition that its composite with the target detached inclusion equals the original detached inclusion followed by the strict-transform isomorphism.
-/
theorem detachedSchemeIso_hom_comp_detachedι (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i < S'.length) :
    (P.detachedSchemeIso i hi).hom ≫ S'.detachedι i = S.detachedι i ≫ (P.strictTransformIso i hi.le).hom :=
  (P.exists_iso_detachedScheme i hi).choose_spec

/- English proof (authored)
The original detached closure is the inverse image of the target detached closure. Taking complements and using that inverse image commutes with complement gives the identity of the two opens.
-/
theorem preimage_detachedClosureCompl (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    (P.strictTransformIso i hi.le).hom ⁻¹ᵁ (S'.detachedClosureCompl i) = S.detachedClosureCompl i := by
  have h : ⇑((P.strictTransformIso i hi.le).hom) ⁻¹' (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) =
      (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) := P.preimage_coe_detachedClosure i hi
  have h2 : ⇑((P.strictTransformIso i hi.le).hom) ⁻¹'
      ((↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i))ᶜ) =
      ((↑(S.detachedClosure i) : Set ↥(S.strictTransform i))ᶜ) := by
    rw [Set.preimage_compl, h]
  exact TopologicalSpace.Opens.ext h2

/- English proof (authored)
The target ambient center is the image ideal of the original center under the stage closed immersion. Pulling that image back along the closed immersion recovers the original center. By the commuting square of strict transforms, pulling back the restriction of the target center is the same as first pulling back along that stage immersion and then restricting to the original strict transform. The result is the original restricted center.
-/
theorem comap_comapAmbientCenter (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    (S'.comapAmbientCenter i).comap (P.strictTransformIso i hi.le).hom = S.comapAmbientCenter i := by
  have hmap : S'.ambientCenter i = (S.ambientCenter i).map (P.levelMap i hi.le) := by
    rw [P.ambientCenter_eq i hi, map_eq_imageIdealSheaf]
  simp only [EmbeddedBlowupSequence.comapAmbientCenter_eq]
  rw [← Scheme.IdealSheafData.comap_comp, P.strictTransformIso_hom_comp_strictTransformι i hi.le,
    Scheme.IdealSheafData.comap_comp, hmap, Blowup.comap_map_of_isClosedImmersion]

/- English proof (authored)
The equality of opens ensures that the forward isomorphism sends the first open into the second and that its inverse sends the second into the first. Restrict both maps using the open inclusions. Their composites are identities by cancellation after the inclusions, and the forward restriction commutes with the inclusions by construction.
-/
private theorem exists_isIso_of_preimage_opens_eq {X Z : Scheme.{u}} (e : X ≅ Z) (U : X.Opens)
    (U' : Z.Opens) (hU : e.hom ⁻¹ᵁ U' = U) :
    ∃ ψ : U.toScheme ⟶ U'.toScheme, IsIso ψ ∧ ψ ≫ U'.ι = U.ι ≫ e.hom := by
  have hfwd : ∀ y : ↥X, y ∈ (U : Set ↥X) → ⇑e.hom.base y ∈ (U' : Set ↥Z) := by
    intro y hy
    have h : y ∈ (↑(e.hom ⁻¹ᵁ U') : Set ↥X) := by rw [hU]; exact hy
    exact h
  have hbwd : ∀ y : ↥X, ⇑e.hom.base y ∈ (U' : Set ↥Z) → y ∈ (U : Set ↥X) := by
    intro y hy
    have h : y ∈ (↑(e.hom ⁻¹ᵁ U') : Set ↥X) := hy
    rwa [hU] at h
  have h1 : Set.range ⇑(U.ι ≫ e.hom).base ⊆ Set.range ⇑U'.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show ⇑e.hom.base (⇑U.ι.base x) ∈ (U' : Set ↥Z)
    exact hfwd _ x.2
  have h2 : Set.range ⇑(U'.ι ≫ e.inv).base ⊆ Set.range ⇑U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    show ⇑e.inv.base (⇑U'.ι.base y) ∈ (U : Set ↥X)
    refine hbwd _ ?_
    have hy : ⇑e.hom.base (⇑e.inv.base (⇑U'.ι.base y)) = ⇑U'.ι.base y :=
      Scheme.inv_hom_apply e (⇑U'.ι.base y)
    rw [hy]
    exact y.2
  refine ⟨IsOpenImmersion.lift U'.ι (U.ι ≫ e.hom) h1, ?_, ?_⟩
  · refine ⟨⟨IsOpenImmersion.lift U.ι (U'.ι ≫ e.inv) h2, ?_, ?_⟩⟩
    · rw [← cancel_mono U.ι, Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
        IsOpenImmersion.lift_fac, Category.assoc, e.hom_inv_id, Category.comp_id,
        Category.id_comp]
    · rw [← cancel_mono U'.ι, Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
        IsOpenImmersion.lift_fac, Category.assoc, e.inv_hom_id, Category.comp_id,
        Category.id_comp]
  · rw [IsOpenImmersion.lift_fac]

/- English proof (authored)
The complements of the detached closures correspond under the strict-transform isomorphism, giving a pullback square of open inclusions. The restricted target ambient center pulls back in this square to the restricted original ambient center by the commuting square and the comparison of ambient centers on strict transforms. The center off the detached locus is the image ideal of that restricted center along the open inclusion. Flat base change allows this image operation to commute with pullback along the isomorphism, which gives the stated equality.
-/
theorem comap_centerOffDetached (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    (S'.centerOffDetached i).comap (P.strictTransformIso i hi.le).hom = S.centerOffDetached i := by
  have hns' : TopologicalSpace.NoetherianSpace ↥(S'.strictTransform i) :=
    S'.noetherianSpace_strictTransform i hi.le
  have hnU : TopologicalSpace.NoetherianSpace ↥((S'.detachedClosureCompl i).toScheme) :=
    Blowup.noetherianSpace_toScheme (S'.strictTransform i) (S'.detachedClosureCompl i)
  have hqc : AlgebraicGeometry.QuasiCompact (S'.detachedClosureCompl i).ι :=
    ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hfl : AlgebraicGeometry.Flat (P.strictTransformIso i hi.le).hom := inferInstance
  obtain ⟨ψ, hψ, hψc⟩ := exists_isIso_of_preimage_opens_eq (P.strictTransformIso i hi.le) (S.detachedClosureCompl i)
    (S'.detachedClosureCompl i) (P.preimage_detachedClosureCompl i hi)
  have := hψ
  have H : IsPullback ψ (S.detachedClosureCompl i).ι (S'.detachedClosureCompl i).ι (P.strictTransformIso i hi.le).hom :=
    IsPullback.of_horiz_isIso ⟨hψc⟩
  have key := comap_map_eq_map_comap_of_isPullback H
    ((S'.comapAmbientCenter i).comap (S'.detachedClosureCompl i).ι)
  have hW : ((S'.comapAmbientCenter i).comap (S'.detachedClosureCompl i).ι).comap ψ
      = (S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι := by
    rw [← Scheme.IdealSheafData.comap_comp, hψc, Scheme.IdealSheafData.comap_comp,
      P.comap_comapAmbientCenter i hi]
  rw [hW] at key
  have hS' : S'.centerOffDetached i
      = ((S'.comapAmbientCenter i).comap (S'.detachedClosureCompl i).ι).map (S'.detachedClosureCompl i).ι :=
    (S'.centerOffDetached_eq i).trans (map_eq_ker_subschemeι_comp _ _).symm
  have hS : S.centerOffDetached i
      = ((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).map (S.detachedClosureCompl i).ι :=
    (S.centerOffDetached_eq i).trans (map_eq_ker_subschemeι_comp _ _).symm
  rw [hS', hS]
  exact key

end ChartPushforward

end FunctorialResolution.EmbeddedResolution

end
