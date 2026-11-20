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

/- English proof (translation)
Establish `hinj : Function.Injective f`. Introduce `a b hab`. Establish `h` using `congrArg g hab`. Rewrite `h` using `[hgf, hgf]`. Then use the resulting hypothesis. Establish `hirrf : ∀ s : Set α, IsIrreducible s → IsIrreducible (f '' s)` using `fun s hs => hs.image f hf.continuousOn`.

Establish `hirrg : ∀ t : Set β, IsIrreducible t → IsIrreducible (g '' t)` using `fun t ht => ht.image g hg.continuousOn`. Establish `himg : g '' (f '' C) = C`. Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce and unpack `x ⟨y, ⟨z, hz, rfl⟩, rfl⟩`. Rewrite using `[hgf]` and apply the resulting hypothesis.

Introduce `x hx`. Conclude with `⟨f x, ⟨x, hx, rfl⟩, hgf x⟩`. Prove the components needed by the constructor for the conclusion. Introduce `hC0`. Establish `hC : IsIrreducible C ∧ ∀ ⦃b : Set α⦄, IsIrreducible b → C ≤ b → b ≤ C` using `hC0`.

Use `show IsIrreducible (f '' C) ∧ ∀ ⦃b : Set β⦄, IsIrreducible b → f '' C ≤ b → b ≤ f '' C`. Use `⟨hirrf C hC.1, ?_⟩` and prove the remaining obligations. Introduce `t ht hsub`. Establish `hsub' : f '' C ⊆ t` using `hsub`. Establish `hCt : C ⊆ g '' t` using `fun x hx => ⟨f x, hsub' ⟨x, hx, rfl⟩, hgf x⟩`.

Establish `hle : g '' t ⊆ C` using `hC.2 (hirrg t ht) hCt`. Introduce `y hy`. Conclude with `⟨g y, hle ⟨y, hy, rfl⟩, hfg y⟩`. Introduce `hC0`. Establish `hC : IsIrreducible (f '' C) ∧ ∀ ⦃b : Set β⦄, IsIrreducible b → f '' C ≤ b → b ≤ f '' C` using `hC0`.

Use `show IsIrreducible C ∧ ∀ ⦃b : Set α⦄, IsIrreducible b → C ≤ b → b ≤ C`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hirrg _ hC.1`. Rewrite `h1` using `[himg]`. Then use the resulting hypothesis. Introduce `t ht hsub`.

Establish `hsub' : C ⊆ t` using `hsub`. Establish `himt : f '' C ⊆ f '' t`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨x, hsub' hx, rfl⟩`. Establish `hle : f '' t ⊆ f '' C` using `hC.2 (hirrf t ht) himt`.

Introduce `x hx`. Take `⟨x', hx', hxx⟩` from `hle ⟨x, hx, rfl⟩`. Establish `hx'x : x' = x` using `hinj hxx`. Rewrite using `[← hx'x]` and apply the resulting hypothesis.
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

/- English proof (translation)
Establish `hgf : ∀ x : ↥(S.strictTransform i), ((P.strictTransformIso i hi.le).inv).base (((P.strictTransformIso i hi.le).hom).base x) = x` using `fun x => Scheme.hom_inv_apply (P.strictTransformIso i hi.le) x`. Establish `hfg : ∀ y : ↥(S'.strictTransform i), ((P.strictTransformIso i hi.le).hom).base (((P.strictTransformIso i hi.le).inv).base y) = y` using `fun y => Scheme.inv_hom_apply (P.strictTransformIso i hi.le) y`. Establish `hcomm : ∀ x : ↥(S.strictTransform i), (S'.strictTransformι i).base (((P.strictTransformIso i hi.le).hom).base x) = (P.levelMap i hi.le).base ((S.strictTransformι i).base x)` using `fun x => congrArg (fun g : S.strictTransform i ⟶ S'.schemeAt i => g.base x) (P.strictTransformIso_hom_comp_strictTransformι i hi.le)`. Establish `hinj` using `(AlgebraicGeometry.Scheme.Hom.isClosedEmbedding (P.levelMap i hi.le)).injective`. Establish `hsupp` using `P.support_ambientCenter_eq_image i hi`.

Simplify using `only [EmbeddedBlowupSequence.mem_detachedComponents]`. Use `and_congr (mem_irreducibleComponents_iff_image (⇑((P.strictTransformIso i hi.le).hom)) (⇑((P.strictTransformIso i hi.le).inv)) (P.strictTransformIso i hi.le).hom.base.hom.continuous (P.strictTransformIso i hi.le).inv.base.hom.continuous hgf hfg C) ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `h z hz`. Take `⟨y, hy, rfl⟩` from `hz`.

Take `⟨x, hxC, rfl⟩` from `hy`. Rewrite using `[hsupp]`. Conclude with `⟨(S.strictTransformι i).base x, h ⟨x, hxC, rfl⟩, (hcomm x).symm⟩`. Introduce `h z hz`. Take `⟨x, hxC, rfl⟩` from `hz`.

Establish `hmem : (S'.strictTransformι i).base (((P.strictTransformIso i hi.le).hom).base x) ∈ ((S'.ambientCenter i).support : Set ↥(S'.schemeAt i))` using `h ⟨((P.strictTransformIso i hi.le).hom).base x, ⟨x, hxC, rfl⟩, rfl⟩`. Rewrite `hmem` using `[hsupp]`. Take `⟨w, hw, hweq⟩` from `hmem`. Establish `hweq' : (P.levelMap i hi.le).base w = (P.levelMap i hi.le).base ((S.strictTransformι i).base x)` using `hweq.trans (hcomm x)`. Establish `hwx : w = (S.strictTransformι i).base x` using `hinj hweq'`.

Rewrite `hw` using `[hwx]`. Then use the resulting hypothesis.
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

/- English proof (translation)
Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce and unpack `x ⟨D, hD, hxD⟩`. Take `⟨y, rfl⟩` from `hf x`. Use `⟨y, ⟨f ⁻¹' D, ?_, hxD⟩, rfl⟩` and prove the remaining obligations. Use `(h (f ⁻¹' D)).mpr ?_` and prove the remaining obligations.

Rewrite using `[Set.image_preimage_eq D hf]`. Conclude with `hD`. Introduce and unpack `z ⟨y, hy, rfl⟩`. Take `⟨C, hC, hyC⟩` from `hy`. Conclude with `⟨f '' C, (h C).mp hC, ⟨y, hyC, rfl⟩⟩`.
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

/- English proof (translation)
Establish `hsurj : Function.Surjective ⇑((P.strictTransformIso i hi.le).hom)` using `(Scheme.homeoOfIso (P.strictTransformIso i hi.le)).surjective`. Rewrite using `[S'.detachedLocus_eq_sUnion i, S.detachedLocus_eq_sUnion i]`. Conclude with `sUnion_eq_image_sUnion _ hsurj _ _ (fun C => P.mem_detachedComponents_iff i hi C)`.
-/
theorem detachedLocus_eq_image (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    S'.detachedLocus i = ⇑((P.strictTransformIso i hi.le).hom) '' S.detachedLocus i := by
  have hsurj : Function.Surjective ⇑((P.strictTransformIso i hi.le).hom) :=
    (Scheme.homeoOfIso (P.strictTransformIso i hi.le)).surjective
  rw [S'.detachedLocus_eq_sUnion i, S.detachedLocus_eq_sUnion i]
  exact sUnion_eq_image_sUnion _ hsurj _ _
    (fun C => P.mem_detachedComponents_iff i hi C)

/- English proof (translation)
Establish `h1 : (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) = closure (S'.detachedLocus i)` using `rfl`. Establish `h2 : (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) = closure (S.detachedLocus i)` using `rfl`. Rewrite using `[h1, h2, P.detachedLocus_eq_image i hi]`. Conclude with `((Scheme.homeoOfIso (P.strictTransformIso i hi.le)).image_closure (S.detachedLocus i)).symm`.
-/
theorem coe_detachedClosure_eq_image (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) =
      ⇑((P.strictTransformIso i hi.le).hom) '' (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) := by
  have h1 : (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) = closure (S'.detachedLocus i) := rfl
  have h2 : (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) = closure (S.detachedLocus i) := rfl
  rw [h1, h2, P.detachedLocus_eq_image i hi]
  exact ((Scheme.homeoOfIso (P.strictTransformIso i hi.le)).image_closure (S.detachedLocus i)).symm

/- English proof (translation)
Rewrite using `[P.coe_detachedClosure_eq_image i hi]`. Conclude with `Set.preimage_image_eq _ (Scheme.homeoOfIso (P.strictTransformIso i hi.le)).injective`.
-/
theorem preimage_coe_detachedClosure (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    ⇑((P.strictTransformIso i hi.le).hom) ⁻¹' (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) =
      (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) := by
  rw [P.coe_detachedClosure_eq_image i hi]
  exact Set.preimage_image_eq _ (Scheme.homeoOfIso (P.strictTransformIso i hi.le)).injective

/- English proof (translation)
Establish `hn' : TopologicalSpace.NoetherianSpace ↥(S'.strictTransform i)` using `S'.noetherianSpace_strictTransform i hi.le`. Establish `hn : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i)` using `S.noetherianSpace_strictTransform i (P.le_length hi.le)`. Establish `hr' : AlgebraicGeometry.IsReduced (S'.strictTransform i)` using `S'.isReduced_strictTransform i hi.le`. Establish `hr : AlgebraicGeometry.IsReduced (S.strictTransform i)` using `S.isReduced_strictTransform i (P.le_length hi.le)`. Establish `hfl : AlgebraicGeometry.Flat (P.strictTransformIso i hi.le).hom` using `inferInstance`.

Establish `hS : S'.detachedComponents i ⊆ irreducibleComponents ↥(S'.strictTransform i)` using `fun C hC => ((S'.mem_detachedComponents i C).mp hC).1`. Establish `hZ : (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) = ⋃₀ (S'.detachedComponents i)` using `(S'.detachedClosure_coe i).trans (S'.detachedLocus_eq_sUnion i)`. Establish `hZ' : (↑(S.detachedClosure i) : Set ↥(S.strictTransform i)) = ⇑((P.strictTransformIso i hi.le).hom).base ⁻¹' (⋃₀ (S'.detachedComponents i))`. Rewrite using `[← hZ]`. Conclude with `(P.preimage_coe_detachedClosure i hi).symm`.

Rewrite using `[S'.detachedIdeal_eq i, S.detachedIdeal_eq i]`. Conclude with `comap_vanishingIdeal_sUnion (P.strictTransformIso i hi.le).hom hS hZ hZ'`.
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

/- English proof (translation)
Establish `h1 : J ≤ I.map e.hom` using `Scheme.IdealSheafData.le_map_iff_comap_le.mpr (le_of_eq h)`. Establish `hcomp : I.comap e.inv = J`. Rewrite using `[← h, ← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]`. Establish `h2 : I ≤ J.map e.inv` using `Scheme.IdealSheafData.le_map_iff_comap_le.mpr (le_of_eq hcomp)`. Take `⟨a, ha⟩ : ∃ a : I.subscheme ⟶ J.subscheme, a ≫ J.subschemeι = I.subschemeι ≫ e.hom` from `⟨I.subschemeMap J e.hom h1, Scheme.IdealSheafData.subschemeMap_subschemeι I J e.hom h1⟩`.

Take `⟨b, hb⟩ : ∃ b : J.subscheme ⟶ I.subscheme, b ≫ I.subschemeι = J.subschemeι ≫ e.inv` from `⟨J.subschemeMap I e.inv h2, Scheme.IdealSheafData.subschemeMap_subschemeι J I e.inv h2⟩`. Use `⟨⟨a, b, ?_, ?_⟩, ha⟩` and prove the remaining obligations. Use `(cancel_mono I.subschemeι).mp ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hb, ← Category.assoc, ha, Category.assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]`. Use `(cancel_mono J.subschemeι).mp ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, ha, ← Category.assoc, hb, Category.assoc, e.inv_hom_id, Category.comp_id, Category.id_comp]`.
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

/- English proof (translation)
Conclude with `exists_subschemeIso_of_comap_eq (P.strictTransformIso i hi.le) (S.detachedIdeal i) (S'.detachedIdeal i) (P.comap_detachedIdeal i hi)`.
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
/- English proof (translation)
The claim follows from `(P.exists_iso_detachedScheme i hi).choose_spec`.
-/
theorem detachedSchemeIso_hom_comp_detachedι (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i < S'.length) :
    (P.detachedSchemeIso i hi).hom ≫ S'.detachedι i = S.detachedι i ≫ (P.strictTransformIso i hi.le).hom :=
  (P.exists_iso_detachedScheme i hi).choose_spec

/- English proof (translation)
Establish `h : ⇑((P.strictTransformIso i hi.le).hom) ⁻¹' (↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i)) = (↑(S.detachedClosure i) : Set ↥(S.strictTransform i))` using `P.preimage_coe_detachedClosure i hi`. Establish `h2 : ⇑((P.strictTransformIso i hi.le).hom) ⁻¹' ((↑(S'.detachedClosure i) : Set ↥(S'.strictTransform i))ᶜ) = ((↑(S.detachedClosure i) : Set ↥(S.strictTransform i))ᶜ)`. Rewrite using `[Set.preimage_compl, h]`. Conclude with `TopologicalSpace.Opens.ext h2`.
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

/- English proof (translation)
Establish `hmap : S'.ambientCenter i = (S.ambientCenter i).map (P.levelMap i hi.le)`. Rewrite using `[P.ambientCenter_eq i hi, map_eq_imageIdealSheaf]`. Simplify using `only [EmbeddedBlowupSequence.comapAmbientCenter_eq]`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, P.strictTransformIso_hom_comp_strictTransformι i hi.le, Scheme.IdealSheafData.comap_comp, hmap, Blowup.comap_map_of_isClosedImmersion]`.
-/
theorem comap_comapAmbientCenter (P : ChartPushforward S S') (i : ℕ) (hi : i < S'.length) :
    (S'.comapAmbientCenter i).comap (P.strictTransformIso i hi.le).hom = S.comapAmbientCenter i := by
  have hmap : S'.ambientCenter i = (S.ambientCenter i).map (P.levelMap i hi.le) := by
    rw [P.ambientCenter_eq i hi, map_eq_imageIdealSheaf]
  simp only [EmbeddedBlowupSequence.comapAmbientCenter_eq]
  rw [← Scheme.IdealSheafData.comap_comp, P.strictTransformIso_hom_comp_strictTransformι i hi.le,
    Scheme.IdealSheafData.comap_comp, hmap, Blowup.comap_map_of_isClosedImmersion]

/- English proof (translation)
Establish `hfwd : ∀ y : ↥X, y ∈ (U : Set ↥X) → ⇑e.hom.base y ∈ (U' : Set ↥Z)`. Introduce `y hy`. Establish `h : y ∈ (↑(e.hom ⁻¹ᵁ U') : Set ↥X)` using `by rw [hU]; exact hy`. Conclude with `h`. Establish `hbwd : ∀ y : ↥X, ⇑e.hom.base y ∈ (U' : Set ↥Z) → y ∈ (U : Set ↥X)`.

Introduce `y hy`. Establish `h : y ∈ (↑(e.hom ⁻¹ᵁ U') : Set ↥X)` using `hy`. Rewrite `h` using `[hU]`. Then use the resulting hypothesis. Establish `h1 : Set.range ⇑(U.ι ≫ e.hom).base ⊆ Set.range ⇑U'.ι.base`. Rewrite using `[Scheme.Opens.range_ι]`.

Introduce and unpack `_ ⟨x, rfl⟩`. Use `show ⇑e.hom.base (⇑U.ι.base x) ∈ (U' : Set ↥Z)`. Conclude with `hfwd _ x.2`. Establish `h2 : Set.range ⇑(U'.ι ≫ e.inv).base ⊆ Set.range ⇑U.ι.base`. Rewrite using `[Scheme.Opens.range_ι]`.

Introduce and unpack `_ ⟨y, rfl⟩`. Use `show ⇑e.inv.base (⇑U'.ι.base y) ∈ (U : Set ↥X)`. Use `hbwd _ ?_` and prove the remaining obligations. Establish `hy : ⇑e.hom.base (⇑e.inv.base (⇑U'.ι.base y)) = ⇑U'.ι.base y` using `Scheme.inv_hom_apply e (⇑U'.ι.base y)`. Rewrite using `[hy]`.

Conclude with `y.2`. Use `⟨IsOpenImmersion.lift U'.ι (U.ι ≫ e.hom) h1, ?_, ?_⟩` and prove the remaining obligations. Use `⟨⟨IsOpenImmersion.lift U.ι (U'.ι ≫ e.inv) h2, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono U.ι, Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]`. Rewrite using `[← cancel_mono U'.ι, Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, e.inv_hom_id, Category.comp_id, Category.id_comp]`.

Rewrite using `[IsOpenImmersion.lift_fac]`.
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

/- English proof (translation)
Establish `hns' : TopologicalSpace.NoetherianSpace ↥(S'.strictTransform i)` using `S'.noetherianSpace_strictTransform i hi.le`. Establish `hnU : TopologicalSpace.NoetherianSpace ↥((S'.detachedClosureCompl i).toScheme)` using `Blowup.noetherianSpace_toScheme (S'.strictTransform i) (S'.detachedClosureCompl i)`. Establish `hqc : AlgebraicGeometry.QuasiCompact (S'.detachedClosureCompl i).ι` using `⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩`. Establish `hfl : AlgebraicGeometry.Flat (P.strictTransformIso i hi.le).hom` using `inferInstance`. Take `⟨ψ, hψ, hψc⟩` from `exists_isIso_of_preimage_opens_eq (P.strictTransformIso i hi.le) (S.detachedClosureCompl i) (S'.detachedClosureCompl i) (P.preimage_detachedClosureCompl i hi)`.

Use `hψ` as an intermediate fact. Establish `H : IsPullback ψ (S.detachedClosureCompl i).ι (S'.detachedClosureCompl i).ι (P.strictTransformIso i hi.le).hom` using `IsPullback.of_horiz_isIso ⟨hψc⟩`. Establish `key` using `comap_map_eq_map_comap_of_isPullback H ((S'.comapAmbientCenter i).comap (S'.detachedClosureCompl i).ι)`. Establish `hW : ((S'.comapAmbientCenter i).comap (S'.detachedClosureCompl i).ι).comap ψ = (S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, hψc, Scheme.IdealSheafData.comap_comp, P.comap_comapAmbientCenter i hi]`.

Rewrite `key` using `[hW]`. Establish `hS' : S'.centerOffDetached i = ((S'.comapAmbientCenter i).comap (S'.detachedClosureCompl i).ι).map (S'.detachedClosureCompl i).ι` using `(S'.centerOffDetached_eq i).trans (map_eq_ker_subschemeι_comp _ _).symm`. Establish `hS : S.centerOffDetached i = ((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).map (S.detachedClosureCompl i).ι` using `(S.centerOffDetached_eq i).trans (map_eq_ker_subschemeι_comp _ _).symm`. Rewrite using `[hS', hS]`. Conclude with `key`.
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
