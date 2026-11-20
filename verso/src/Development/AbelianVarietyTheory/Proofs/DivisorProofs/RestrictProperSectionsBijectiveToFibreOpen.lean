import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

/- English proof (translation)
Introduce `Y₀ H X'' P'' H' i a'' b'' hY hi ha hs hV hb`. Use `haveI := hY`. Use `haveI := hi`. Use `haveI := ha`. Use `haveI := hs`.

Use `haveI := hb`. Establish `hP : IsNoetherian P''` using `by haveI : IsLocallyNoetherian P'' := LocallyOfFiniteType.isLocallyNoetherian b'' haveI : CompactSpace P'' := QuasiCompact.compactSpace_of_compactSpace b''`. Conclude with `{}`. Set `U0 : P''.Opens` to `⟨(a'' '' (Set.range i)ᶜ)ᶜ, (a''.isClosedMap _ i.isOpenEmbedding.isOpen_range.isClosed_compl).isOpen_compl⟩`. Establish `hsub : ∀ w : X'', a'' w ∈ U0 → w ∈ Set.range i`.

Introduce `w hw`. Assume the negation of the conclusion as `h`. Conclude with `hw ⟨w, h, rfl⟩`. Set `W : H'.toScheme.Opens` to `i ⁻¹ᵁ (a'' ⁻¹ᵁ U0)`. Set `X : H.Opens` to `H'.ι ''ᵁ W`.

Establish `hXr : Set.range X.ι ⊆ Set.range H'.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨z, -, rfl⟩`. Conclude with `⟨z, rfl⟩`. Set `k : X.toScheme ⟶ H'.toScheme` to `IsOpenImmersion.lift H'.ι X.ι hXr`.

Establish `hk : k ≫ H'.ι = X.ι` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hrk : Set.range k = (W : Set H'.toScheme)`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`.

Establish `h1 : H'.ι (k y) ∈ X`. Rewrite using `[← Scheme.Hom.comp_apply, hk]`. Establish `: X.ι y ∈ Set.range X.ι` using `⟨y, rfl⟩`. Rewrite `this` using `[Scheme.Opens.range_ι]`. Then use the resulting hypothesis. Take `⟨w, hw, he⟩` from `h1`.

Rewrite using `[← H'.ι.isOpenEmbedding.injective he]` and apply the resulting hypothesis. Introduce `hz`. Establish `: H'.ι z ∈ Set.range X.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `⟨z, hz, rfl⟩`.

Take `⟨y, hy⟩` from `this`. Use `⟨y, H'.ι.isOpenEmbedding.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hk, hy]`. Establish `hrki : Set.range (k ≫ i) = (a'' ⁻¹ᵁ U0 : Set X'')`. Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrk]`.

Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `hz`. Introduce `hw`.

Take `⟨z, rfl⟩` from `hsub w hw`. Conclude with `⟨z, hw, rfl⟩`. Set `e` to `IsOpenImmersion.isoOfRangeEq (k ≫ i) (a'' ⁻¹ᵁ U0).ι (by rw [Scheme.Opens.range_ι]; exact hrki)`. Set `a : X.toScheme ⟶ U0.toScheme` to `e.hom ≫ (a'' ∣_ U0)`. Establish `hfac : a ≫ U0.ι = k ≫ i ≫ a''`.

Simplify using `only [a, e, Category.assoc, morphismRestrict_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]`. Use `⟨U0.toScheme, U0.ι, X, k, a, inferInstance, ?_, inferInstance, ?_, ?_, hk, hfac, ?_, ?_⟩` and prove the remaining obligations. Use `haveI := hP haveI : CompactSpace U0.toScheme := QuasiCompact.compactSpace_of_compactSpace U0.ι`. Conclude with `{}`. Use `⟨fun x => ?_⟩` and prove the remaining obligations.

Take `⟨w, hw⟩` from `a''.surjective x.1`. Establish `hw' : w ∈ Set.range (k ≫ i)`. Rewrite using `[hrki]`. Use `show a'' w ∈ U0`. Rewrite using `[hw]`.

Conclude with `x.2`. Take `⟨y, rfl⟩` from `hw'`. Use `⟨y, U0.ι.isOpenEmbedding.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hfac]`. Simplify using `only [Scheme.Hom.comp_apply] at hw ⊢`.

Rewrite using `[hw]`. Both sides reduce to the same expression. Introduce `V show Function.Bijective ((e.hom ≫ (a'' ∣_ U0)).app V).hom`. Rewrite using `[Scheme.Hom.comp_app]`. Establish `h1 : Function.Bijective ((a'' ∣_ U0).app V).hom`.

Rewrite using `[morphismRestrict_app]`. Establish `h3` using `hV (U0.ι ''ᵁ V)`. Establish `h4 : Function.Bijective (X''.presheaf.map (eqToHom (image_morphismRestrict_preimage a'' U0 V)).op).hom` using `ConcreteCategory.bijective_of_isIso _`. Conclude with `h4.comp h3`. Establish `h2 : Function.Bijective (e.hom.app ((a'' ∣_ U0) ⁻¹ᵁ V)).hom` using `ConcreteCategory.bijective_of_isIso _`.

Conclude with `h2.comp h1`. Introduce `z hz`. Establish `: z ∈ W` using `by show a'' (i z) ∈ U0`. Introduce and unpack `⟨w, hw, he⟩`. Conclude with `hw (hz w he)`.

Conclude with `⟨z, this, rfl⟩`. Introduce `w hw`. Rewrite using `[hrki]`. Rewrite `hw` using `[Scheme.Opens.range_ι]`. Conclude with `hw`.
-/
theorem restrict_proper_sections_bijective_to_fibre_open : ∀ (Y₀ H X'' P'' : Scheme.{0}) (H' : H.Opens) (i : H'.toScheme ⟶ X'') (a'' : X'' ⟶ P'') (b'' : P'' ⟶ Y₀), IsNoetherian Y₀ → IsOpenImmersion i → IsProper a'' → Surjective a'' → (∀ V : P''.Opens, Function.Bijective (a''.app V).hom) → IsFinite b'' → ∃ (P' : Scheme.{0}) (c : P' ⟶ P'') (X : H.Opens) (k : X.toScheme ⟶ H'.toScheme) (a : X.toScheme ⟶ P'), IsOpenImmersion c ∧ IsNoetherian P' ∧ IsProper a ∧ Surjective a ∧ (∀ V : P'.Opens, Function.Bijective (a.app V).hom) ∧ k ≫ H'.ι = X.ι ∧ a ≫ c = k ≫ i ≫ a'' ∧ (∀ z : H'.toScheme, (∀ w : X'', a'' w = a'' (i z) → w ∈ Set.range i) → H'.ι z ∈ X) ∧ ∀ w : X'', a'' w ∈ Set.range c → w ∈ Set.range (k ≫ i) := by
  intro Y₀ H X'' P'' H' i a'' b'' hY hi ha hs hV hb
  haveI := hY; haveI := hi; haveI := ha; haveI := hs; haveI := hb
  have hP : IsNoetherian P'' := by
    haveI : IsLocallyNoetherian P'' := LocallyOfFiniteType.isLocallyNoetherian b''
    haveI : CompactSpace P'' := QuasiCompact.compactSpace_of_compactSpace b''
    exact {}
  let U0 : P''.Opens := ⟨(a'' '' (Set.range i)ᶜ)ᶜ,
    (a''.isClosedMap _ i.isOpenEmbedding.isOpen_range.isClosed_compl).isOpen_compl⟩
  have hsub : ∀ w : X'', a'' w ∈ U0 → w ∈ Set.range i := by
    intro w hw
    by_contra h
    exact hw ⟨w, h, rfl⟩
  let W : H'.toScheme.Opens := i ⁻¹ᵁ (a'' ⁻¹ᵁ U0)
  let X : H.Opens := H'.ι ''ᵁ W
  have hXr : Set.range X.ι ⊆ Set.range H'.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  let k : X.toScheme ⟶ H'.toScheme := IsOpenImmersion.lift H'.ι X.ι hXr
  have hk : k ≫ H'.ι = X.ι := IsOpenImmersion.lift_fac _ _ _
  have hrk : Set.range k = (W : Set H'.toScheme) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      have h1 : H'.ι (k y) ∈ X := by
        rw [← Scheme.Hom.comp_apply, hk]
        have : X.ι y ∈ Set.range X.ι := ⟨y, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
      obtain ⟨w, hw, he⟩ := h1
      rwa [← H'.ι.isOpenEmbedding.injective he]
    · intro hz
      have : H'.ι z ∈ Set.range X.ι := by
        rw [Scheme.Opens.range_ι]; exact ⟨z, hz, rfl⟩
      obtain ⟨y, hy⟩ := this
      refine ⟨y, H'.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hk, hy]
  have hrki : Set.range (k ≫ i) = (a'' ⁻¹ᵁ U0 : Set X'') := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrk]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro hw
      obtain ⟨z, rfl⟩ := hsub w hw
      exact ⟨z, hw, rfl⟩
  let e := IsOpenImmersion.isoOfRangeEq (k ≫ i) (a'' ⁻¹ᵁ U0).ι (by rw [Scheme.Opens.range_ι]; exact hrki)
  let a : X.toScheme ⟶ U0.toScheme := e.hom ≫ (a'' ∣_ U0)
  have hfac : a ≫ U0.ι = k ≫ i ≫ a'' := by
    simp only [a, e, Category.assoc, morphismRestrict_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
  refine ⟨U0.toScheme, U0.ι, X, k, a, inferInstance, ?_, inferInstance, ?_, ?_, hk, hfac, ?_, ?_⟩
  · haveI := hP
    haveI : CompactSpace U0.toScheme := QuasiCompact.compactSpace_of_compactSpace U0.ι
    exact {}
  · refine ⟨fun x => ?_⟩
    obtain ⟨w, hw⟩ := a''.surjective x.1
    have hw' : w ∈ Set.range (k ≫ i) := by
      rw [hrki]; show a'' w ∈ U0; rw [hw]; exact x.2
    obtain ⟨y, rfl⟩ := hw'
    refine ⟨y, U0.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hfac]
    simp only [Scheme.Hom.comp_apply] at hw ⊢
    rw [hw]; rfl
  · intro V
    show Function.Bijective ((e.hom ≫ (a'' ∣_ U0)).app V).hom
    rw [Scheme.Hom.comp_app]
    have h1 : Function.Bijective ((a'' ∣_ U0).app V).hom := by
      rw [morphismRestrict_app]
      have h3 := hV (U0.ι ''ᵁ V)
      have h4 : Function.Bijective (X''.presheaf.map (eqToHom (image_morphismRestrict_preimage a'' U0 V)).op).hom :=
        ConcreteCategory.bijective_of_isIso _
      exact h4.comp h3
    have h2 : Function.Bijective (e.hom.app ((a'' ∣_ U0) ⁻¹ᵁ V)).hom := ConcreteCategory.bijective_of_isIso _
    exact h2.comp h1
  · intro z hz
    have : z ∈ W := by
      show a'' (i z) ∈ U0
      rintro ⟨w, hw, he⟩
      exact hw (hz w he)
    exact ⟨z, this, rfl⟩
  · intro w hw
    rw [hrki]
    rw [Scheme.Opens.range_ι] at hw
    exact hw

end GlobalTheory
