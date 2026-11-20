import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.MemberGlue

/- English proof (translation)
Introduce `P ι _ C _ _ h W h' _ hh hcl hag`. Establish `hpt : ∀ a c, (W a).ι (h' a c) = h a c` using `fun a c => by rw [← hh a]; rfl`. Set `U : P.Opens` to `⨆ a, W a`. Set `Φ : Set P` to `⋃ a, Set.range (h a)`. Set `O : ι → Set P` to `fun a => (W a).ι '' (Set.range (h' a))ᶜ`.

Establish `hO : ∀ a, IsOpen (O a)` using `fun a => (W a).ι.isOpenEmbedding.isOpenMap _ (h' a).isClosedEmbedding.isClosed_range.isOpen_compl`. Establish `hW : ∀ a c, h a c ∈ (W a : Set P)` using `fun a c => by`. Rewrite using `[← hpt a c]`. Conclude with `(h' a c).2`. Establish `hU : ∀ a, (W a : Set P) ⊆ U` using `fun a => SetLike.coe_subset_coe.mpr (le_iSup W a)`.

Establish `hΦ : U.ι ⁻¹' Φ = (U.ι ⁻¹' ⋃ a, O a)ᶜ`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_compl_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hx hxO`.

Take `⟨a', c', hc'⟩` from `Set.mem_iUnion.mp hx`. Take `⟨a, w, hw, e⟩` from `Set.mem_iUnion.mp hxO |>.imp fun _ h => h`. Establish `h1 : U.ι x ∈ Set.range (h a') ∩ (W a : Set P)` using `⟨⟨c', hc'⟩, e ▸ w.2⟩`. Take `⟨c, hc⟩` from `hag a a' h1`. Conclude with `hw ⟨c, (W a).ι.isOpenEmbedding.injective ((hpt a c).trans (hc.trans e.symm))⟩`.

Introduce `hx`. Take `⟨a, ha⟩` from `TopologicalSpace.Opens.mem_iSup.mp x.2`. Establish `h2 : (⟨x.1, ha⟩ : (W a).toScheme) ∈ Set.range (h' a)`. Assume the negation of the conclusion as `hn`. Conclude with `hx (Set.mem_iUnion.mpr ⟨a, ⟨x.1, ha⟩, hn, rfl⟩)`.

Take `⟨c, hc⟩` from `h2`. Conclude with `Set.mem_iUnion.mpr ⟨a, c, by rw [← hpt a c, hc]; rfl⟩`. Set `Z : TopologicalSpace.Closeds U.toScheme` to `⟨U.ι ⁻¹' Φ, by`. Rewrite using `[hΦ]`. Conclude with `((isOpen_iUnion hO).preimage U.ι.continuous).isClosed_compl⟩`.

Set `I` to `Scheme.IdealSheafData.vanishingIdeal Z`. Set `g : I.subscheme ⟶ U.toScheme` to `I.subschemeι`. Set `f : I.subscheme ⟶ P` to `g ≫ U.ι`. Establish `hrg : Set.range g = Z`. Rewrite using `[Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]`.

Establish `hfΦ : ∀ x, f x ∈ Φ` using `fun x => by`. Establish `: g x ∈ (Z : Set U.toScheme)` using `hrg ▸ ⟨x, rfl⟩`. Conclude with `this`. Establish `hfinj : Function.Injective f` using `f.isEmbedding.injective`. Establish `hrU : ∀ a, Set.range (h a) ⊆ Set.range U.ι` using `fun a => by`.

Introduce and unpack `_ ⟨c, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hU a (hW a c)`. Set `k : ∀ a, C a ⟶ U.toScheme` to `fun a => IsOpenImmersion.lift U.ι (h a) (hrU a)`. Establish `hk : ∀ a, k a ≫ U.ι = h a` using `fun a => IsOpenImmersion.lift_fac _ _ _`.

Establish `hkZ : ∀ a, Set.range (k a) ⊆ Z` using `fun a => by`. Introduce and unpack `_ ⟨c, rfl⟩`. Express the relevant statement in the definitionally equal form `U.ι (k a c) ∈ Φ`. Establish `: U.ι (k a c) = h a c` using `by rw [← hk a]; rfl`. Rewrite using `[this]`.

Conclude with `Set.mem_iUnion.mpr ⟨a, c, rfl⟩`. Establish `hker : ∀ a, g.ker ≤ (k a).ker` using `fun a => by`. Rewrite using `[Scheme.IdealSheafData.ker_subschemeι]`. Conclude with `ReducedSubgroup.vanishingIdeal_le_ker (k a) Z (hkZ a)`. Set `i : ∀ a, C a ⟶ I.subscheme` to `fun a => IsClosedImmersion.lift g (k a) (hker a)`.

Establish `hig : ∀ a, i a ≫ g = k a` using `fun a => IsClosedImmersion.lift_fac _ _ _`. Establish `hif : ∀ a, i a ≫ f = h a` using `fun a => by`. Rewrite using `[← hk a, ← hig a, Category.assoc]`. Establish `hipt : ∀ a c, f (i a c) = h a c` using `fun a c => by rw [← hif a]; rfl`. Establish `: IsReduced I.subscheme` using `ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z`.

Use `⟨I.subscheme, f, i, inferInstance, fun a => ?_, hif, fun x => ?_⟩` and prove the remaining obligations. Set `V : I.subscheme.Opens` to `f ⁻¹ᵁ W a`. Establish `hiV : Set.range (i a) ⊆ Set.range V.ι`. Introduce and unpack `_ ⟨c, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Express the relevant statement in the definitionally equal form `f (i a c) ∈ W a`. Rewrite using `[hipt]`. Conclude with `hW a c`. Establish `hrW : Set.range (V.ι ≫ f) ⊆ Set.range (W a).ι`. Introduce and unpack `_ ⟨y, rfl⟩`.

Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `y.2`. Set `j : C a ⟶ V.toScheme` to `IsOpenImmersion.lift V.ι (i a) hiV`. Establish `hj : j ≫ V.ι = i a` using `IsOpenImmersion.lift_fac _ _ _`. Set `r : V.toScheme ⟶ (W a).toScheme` to `IsOpenImmersion.lift (W a).ι (V.ι ≫ f) hrW`.

Establish `hr : r ≫ (W a).ι = V.ι ≫ f` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hjr : j ≫ r = h' a`. Rewrite using `[← cancel_mono (W a).ι, Category.assoc, hr, reassoc_of% hj, hif, hh]`. Establish `: Mono r`. Establish `: Mono (r ≫ (W a).ι)` using `by rw [hr]; infer_instance`.

Conclude with `mono_of_mono r (W a).ι`. Establish `: IsClosedImmersion (j ≫ r)` using `by rw [hjr]; infer_instance`. Establish `: IsClosedImmersion j` using `IsClosedImmersion.of_comp j r`. Establish `: Surjective j` using `⟨fun y => by`. Establish `hy : f (V.ι y) ∈ (W a : Set P)` using `y.2`.

Take `⟨a', c', hc'⟩` from `Set.mem_iUnion.mp (hfΦ (V.ι y))`. Take `⟨c, hc⟩` from `hag a a' ⟨⟨c', hc'⟩, hy⟩`. Use `⟨c, V.ι.isOpenEmbedding.injective (hfinj ?_)⟩` and prove the remaining obligations. Establish `: V.ι (j c) = i a c` using `by rw [← hj]; rfl`. Rewrite using `[this, hipt, hc]⟩`.

Establish `: IsIso j` using `isIso_of_isClosedImmersion_of_surjective j`. Rewrite using `[← hj]`. Use `infer_instance`. Take `⟨a, c, hc⟩` from `Set.mem_iUnion.mp (hfΦ x)`. Conclude with `⟨a, c, hfinj ((hipt a c).trans hc)⟩`.
-/
theorem exists_immersion_of_closed_pieces : ∀ (P : Scheme.{0}) (ι : Type) [Finite ι] (C : ι → Scheme.{0}) [∀ a, IsAffine (C a)] [∀ a, IsReduced (C a)] (h : ∀ a, C a ⟶ P) (W : ι → P.Opens) (h' : ∀ a, C a ⟶ (W a).toScheme), IsLocallyNoetherian P → (∀ a, h' a ≫ (W a).ι = h a) → (∀ a, IsClosedImmersion (h' a)) → (∀ a a', Set.range (h a') ∩ (W a : Set P) ⊆ Set.range (h a)) → ∃ (F : Scheme.{0}) (f : F ⟶ P) (i : ∀ a, C a ⟶ F), IsImmersion f ∧ (∀ a, IsOpenImmersion (i a)) ∧ (∀ a, i a ≫ f = h a) ∧ ∀ x : F, ∃ a, x ∈ Set.range (i a) := by
  intro P ι _ C _ _ h W h' _ hh hcl hag
  have hpt : ∀ a c, (W a).ι (h' a c) = h a c := fun a c => by rw [← hh a]; rfl
  let U : P.Opens := ⨆ a, W a
  let Φ : Set P := ⋃ a, Set.range (h a)
  let O : ι → Set P := fun a => (W a).ι '' (Set.range (h' a))ᶜ
  have hO : ∀ a, IsOpen (O a) := fun a =>
    (W a).ι.isOpenEmbedding.isOpenMap _ (h' a).isClosedEmbedding.isClosed_range.isOpen_compl
  have hW : ∀ a c, h a c ∈ (W a : Set P) := fun a c => by
    rw [← hpt a c]; exact (h' a c).2
  have hU : ∀ a, (W a : Set P) ⊆ U := fun a =>
    SetLike.coe_subset_coe.mpr (le_iSup W a)
  have hΦ : U.ι ⁻¹' Φ = (U.ι ⁻¹' ⋃ a, O a)ᶜ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro hx hxO
      obtain ⟨a', c', hc'⟩ := Set.mem_iUnion.mp hx
      obtain ⟨a, w, hw, e⟩ := Set.mem_iUnion.mp hxO |>.imp fun _ h => h
      have h1 : U.ι x ∈ Set.range (h a') ∩ (W a : Set P) :=
        ⟨⟨c', hc'⟩, e ▸ w.2⟩
      obtain ⟨c, hc⟩ := hag a a' h1
      exact hw ⟨c, (W a).ι.isOpenEmbedding.injective ((hpt a c).trans (hc.trans e.symm))⟩
    · intro hx
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
      have h2 : (⟨x.1, ha⟩ : (W a).toScheme) ∈ Set.range (h' a) := by
        by_contra hn
        exact hx (Set.mem_iUnion.mpr ⟨a, ⟨x.1, ha⟩, hn, rfl⟩)
      obtain ⟨c, hc⟩ := h2
      exact Set.mem_iUnion.mpr ⟨a, c, by rw [← hpt a c, hc]; rfl⟩
  let Z : TopologicalSpace.Closeds U.toScheme := ⟨U.ι ⁻¹' Φ, by
    rw [hΦ]
    exact ((isOpen_iUnion hO).preimage U.ι.continuous).isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let g : I.subscheme ⟶ U.toScheme := I.subschemeι
  let f : I.subscheme ⟶ P := g ≫ U.ι
  have hrg : Set.range g = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hfΦ : ∀ x, f x ∈ Φ := fun x => by
    have : g x ∈ (Z : Set U.toScheme) := hrg ▸ ⟨x, rfl⟩
    exact this
  have hfinj : Function.Injective f := f.isEmbedding.injective
  have hrU : ∀ a, Set.range (h a) ⊆ Set.range U.ι := fun a => by
    rintro _ ⟨c, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hU a (hW a c)
  let k : ∀ a, C a ⟶ U.toScheme := fun a => IsOpenImmersion.lift U.ι (h a) (hrU a)
  have hk : ∀ a, k a ≫ U.ι = h a := fun a => IsOpenImmersion.lift_fac _ _ _
  have hkZ : ∀ a, Set.range (k a) ⊆ Z := fun a => by
    rintro _ ⟨c, rfl⟩
    change U.ι (k a c) ∈ Φ
    have : U.ι (k a c) = h a c := by rw [← hk a]; rfl
    rw [this]
    exact Set.mem_iUnion.mpr ⟨a, c, rfl⟩
  have hker : ∀ a, g.ker ≤ (k a).ker := fun a => by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact ReducedSubgroup.vanishingIdeal_le_ker (k a) Z (hkZ a)
  let i : ∀ a, C a ⟶ I.subscheme := fun a => IsClosedImmersion.lift g (k a) (hker a)
  have hig : ∀ a, i a ≫ g = k a := fun a => IsClosedImmersion.lift_fac _ _ _
  have hif : ∀ a, i a ≫ f = h a := fun a => by
    rw [← hk a, ← hig a, Category.assoc]
  have hipt : ∀ a c, f (i a c) = h a c := fun a c => by rw [← hif a]; rfl
  have : IsReduced I.subscheme := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  refine ⟨I.subscheme, f, i, inferInstance, fun a => ?_, hif, fun x => ?_⟩
  · let V : I.subscheme.Opens := f ⁻¹ᵁ W a
    have hiV : Set.range (i a) ⊆ Set.range V.ι := by
      rintro _ ⟨c, rfl⟩
      rw [Scheme.Opens.range_ι]
      change f (i a c) ∈ W a
      rw [hipt]
      exact hW a c
    have hrW : Set.range (V.ι ≫ f) ⊆ Set.range (W a).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact y.2
    let j : C a ⟶ V.toScheme := IsOpenImmersion.lift V.ι (i a) hiV
    have hj : j ≫ V.ι = i a := IsOpenImmersion.lift_fac _ _ _
    let r : V.toScheme ⟶ (W a).toScheme := IsOpenImmersion.lift (W a).ι (V.ι ≫ f) hrW
    have hr : r ≫ (W a).ι = V.ι ≫ f := IsOpenImmersion.lift_fac _ _ _
    have hjr : j ≫ r = h' a := by
      rw [← cancel_mono (W a).ι, Category.assoc, hr, reassoc_of% hj, hif, hh]
    have : Mono r := by
      have : Mono (r ≫ (W a).ι) := by rw [hr]; infer_instance
      exact mono_of_mono r (W a).ι
    have : IsClosedImmersion (j ≫ r) := by rw [hjr]; infer_instance
    have : IsClosedImmersion j := IsClosedImmersion.of_comp j r
    have : Surjective j := ⟨fun y => by
      have hy : f (V.ι y) ∈ (W a : Set P) := y.2
      obtain ⟨a', c', hc'⟩ := Set.mem_iUnion.mp (hfΦ (V.ι y))
      obtain ⟨c, hc⟩ := hag a a' ⟨⟨c', hc'⟩, hy⟩
      refine ⟨c, V.ι.isOpenEmbedding.injective (hfinj ?_)⟩
      have : V.ι (j c) = i a c := by rw [← hj]; rfl
      rw [this, hipt, hc]⟩
    have : IsIso j := isIso_of_isClosedImmersion_of_surjective j
    rw [← hj]
    infer_instance
  · obtain ⟨a, c, hc⟩ := Set.mem_iUnion.mp (hfΦ x)
    exact ⟨a, c, hfinj ((hipt a c).trans hc)⟩

end GlobalTheory.MemberGlue
