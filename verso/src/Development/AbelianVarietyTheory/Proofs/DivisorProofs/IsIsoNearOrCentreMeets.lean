import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.SeqFirst

/- English proof (translation)
Establish `e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V`. Rewrite using `[Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]`. Conclude with `inf_eq_right.2 hVU`. Establish `h1 : IsIso ((s ∣_ U) ∣_ (U.ι ⁻¹ᵁ V))` using `inferInstance`. Conclude with `((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictRestrict s U (U.ι ⁻¹ᵁ V) ≪≫ morphismRestrictEq s e)).1 h1`.
-/
theorem isIso_restrict_of_le {X Y : Scheme.{0}} (s : X ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U)
    [IsIso (s ∣_ U)] : IsIso (s ∣_ V) := by
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hVU
  have h1 : IsIso ((s ∣_ U) ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict s U (U.ι ⁻¹ᵁ V) ≪≫ morphismRestrictEq s e)).1 h1

/- English proof (translation)
Take `⟨z, hz⟩` from `(s ∣_ U).homeomorph.surjective ⟨y, hy⟩`. Use `⟨z.1, z.2, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hz` as an intermediate fact. Rewrite using `[← morphismRestrict_base_coe]`. Conclude with `this`.
-/
theorem exists_preimage {X Y : Scheme.{0}} (s : X ⟶ Y) {U : Y.Opens} [IsIso (s ∣_ U)] {y : Y} (hy : y ∈ U) :
    ∃ x ∈ s ⁻¹ᵁ U, s x = y := by
  obtain ⟨z, hz⟩ := (s ∣_ U).homeomorph.surjective ⟨y, hy⟩
  refine ⟨z.1, z.2, ?_⟩
  have := congrArg Subtype.val hz
  rw [← morphismRestrict_base_coe]
  exact this

/- English proof (translation)
Take `⟨za, rfl⟩ : ∃ z : ↥(s ⁻¹ᵁ U).toScheme, z.1 = a` from `⟨⟨a, ha⟩, rfl⟩`. Take `⟨zb, rfl⟩ : ∃ z : ↥(s ⁻¹ᵁ U).toScheme, z.1 = b` from `⟨⟨b, hb⟩, rfl⟩`. Establish `: (s ∣_ U) za = (s ∣_ U) zb` using `Subtype.ext ((morphismRestrict_base_coe s U za).trans (h.trans (morphismRestrict_base_coe s U zb).symm))`. Conclude with `congrArg Subtype.val ((s ∣_ U).homeomorph.injective this)`.
-/
theorem injOn {X Y : Scheme.{0}} (s : X ⟶ Y) {U : Y.Opens} [IsIso (s ∣_ U)] {a b : X}
    (ha : a ∈ s ⁻¹ᵁ U) (hb : b ∈ s ⁻¹ᵁ U) (h : s a = s b) : a = b := by
  obtain ⟨za, rfl⟩ : ∃ z : ↥(s ⁻¹ᵁ U).toScheme, z.1 = a := ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨zb, rfl⟩ : ∃ z : ↥(s ⁻¹ᵁ U).toScheme, z.1 = b := ⟨⟨b, hb⟩, rfl⟩
  have : (s ∣_ U) za = (s ∣_ U) zb :=
    Subtype.ext ((morphismRestrict_base_coe s U za).trans (h.trans (morphismRestrict_base_coe s U zb).symm))
  exact congrArg Subtype.val ((s ∣_ U).homeomorph.injective this)

/- English proof (translation)
Establish `h1 : IsOpenMap (fun z : (s ⁻¹ᵁ U) => s z.1)`. Establish `: (fun z : (s ⁻¹ᵁ U) => s z.1) = (fun w : U => w.1) ∘ (s ∣_ U)`. Use function extensionality and compare the values at `z`. Conclude with `(morphismRestrict_base_coe s U z).symm`. Rewrite using `[this]`.

Conclude with `U.isOpenEmbedding'.isOpenMap.comp (s ∣_ U).homeomorph.isOpenMap`. Establish `h2 : s '' (A ∩ s ⁻¹ᵁ U) = (fun z : (s ⁻¹ᵁ U) => s z.1) '' ((fun z : (s ⁻¹ᵁ U) => z.1) ⁻¹' A)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, ⟨hxA, hxU⟩, rfl⟩`.

Conclude with `⟨⟨x, hxU⟩, hxA, rfl⟩`. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z.1, ⟨hz, z.2⟩, rfl⟩`. Rewrite using `[h2]`. Conclude with `h1 _ (hA.preimage continuous_subtype_val)`.
-/
theorem isOpen_image {X Y : Scheme.{0}} (s : X ⟶ Y) {U : Y.Opens} [IsIso (s ∣_ U)] {A : Set X}
    (hA : IsOpen A) : IsOpen (s '' (A ∩ s ⁻¹ᵁ U)) := by
  have h1 : IsOpenMap (fun z : (s ⁻¹ᵁ U) => s z.1) := by
    have : (fun z : (s ⁻¹ᵁ U) => s z.1) = (fun w : U => w.1) ∘ (s ∣_ U) := by
      funext z; exact (morphismRestrict_base_coe s U z).symm
    rw [this]
    exact U.isOpenEmbedding'.isOpenMap.comp (s ∣_ U).homeomorph.isOpenMap
  have h2 : s '' (A ∩ s ⁻¹ᵁ U) = (fun z : (s ⁻¹ᵁ U) => s z.1) '' ((fun z : (s ⁻¹ᵁ U) => z.1) ⁻¹' A) := by
    ext y; constructor
    · rintro ⟨x, ⟨hxA, hxU⟩, rfl⟩; exact ⟨⟨x, hxU⟩, hxA, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z.1, ⟨hz, z.2⟩, rfl⟩
  rw [h2]
  exact h1 _ (hA.preimage continuous_subtype_val)

end GlobalTheory.SeqFirst

open GlobalTheory.SeqFirst in

/- English proof (translation)
Introduce `S Y f B y Y' s h`. Proceed by induction on `h with`. Consider the case `id => exact Or.inl ⟨⊤, trivial, inferInstance⟩`. Consider the case `@step Y₁ Y₂ s J π hs h₁ h₂ h₃ ih`. Break down `ih with ⟨U, hyU, hU⟩ | hr` into its components or cases.

Take `⟨y', hy'U, hy'⟩` from `exists_preimage s hyU`. Distinguish the cases in `hJ : y' ∈ J.support`. Conclude with `Or.inr ⟨Y₁, s, J, U, y', hs, h₁, h₂, hyU, hU, hJ, hy'⟩`. Use `left`. Establish `hA : IsOpen ((J.support : Set Y₁)ᶜ)` using `J.support.isClosed.isOpen_compl`.

Set `V : Y.Opens` to `⟨s '' ((J.support : Set Y₁)ᶜ ∩ s ⁻¹ᵁ U), isOpen_image s hA⟩`. Establish `hVU : V ≤ U`. Introduce and unpack `_ ⟨x, ⟨-, hx⟩, rfl⟩`. Conclude with `hx`. Establish `hyV : y ∈ V` using `⟨y', ⟨hJ, hy'U⟩, hy'⟩`.

Use `⟨V, hyV, ?_⟩` and prove the remaining obligations. Establish `: IsIso (s ∣_ V)` using `isIso_restrict_of_le s hVU`. Establish `hπ : IsIso (π ∣_ (s ⁻¹ᵁ V))`. Use `Principalise.isIso_restrict_of_blowup h₃ _ ?_` and prove the remaining obligations. Introduce `x hx hxJ`.

Establish `hxU : x ∈ s ⁻¹ᵁ U` using `hVU hx`. Take `⟨w, ⟨hwA, hwU⟩, hw⟩` from `(hx : s x ∈ V)`. Conclude with `hwA (injOn s hwU hxU hw ▸ hxJ)`. Rewrite using `[morphismRestrict_comp]`. Conclude with `IsIso.comp_isIso' hπ this`.

Use `right`. Conclude with `hr`.
-/
theorem GlobalTheory.isIso_near_or_centre_meets : ∀ {S Y : Scheme.{0}} (f : Y ⟶ S) (B : Set Y) (y : Y) {Y' : Scheme.{0}} (s : Y' ⟶ Y), GlobalTheory.IsSmoothBlowupSeq f B s → (∃ U : Y.Opens, y ∈ U ∧ IsIso (s ∣_ U)) ∨ ∃ (Y₁ : Scheme.{0}) (s₁ : Y₁ ⟶ Y) (J : Y₁.IdealSheafData) (U : Y.Opens) (y₁ : Y₁), GlobalTheory.IsSmoothBlowupSeq f B s₁ ∧ Smooth (J.subschemeι ≫ s₁ ≫ f) ∧ (J.support : Set Y₁) ⊆ s₁ ⁻¹' B ∧ y ∈ U ∧ IsIso (s₁ ∣_ U) ∧ y₁ ∈ J.support ∧ s₁ y₁ = y := by
  intro S Y f B y Y' s h
  induction h with
  | id => exact Or.inl ⟨⊤, trivial, inferInstance⟩
  | @step Y₁ Y₂ s J π hs h₁ h₂ h₃ ih =>
    rcases ih with ⟨U, hyU, hU⟩ | hr
    · obtain ⟨y', hy'U, hy'⟩ := exists_preimage s hyU
      by_cases hJ : y' ∈ J.support
      · exact Or.inr ⟨Y₁, s, J, U, y', hs, h₁, h₂, hyU, hU, hJ, hy'⟩
      · left
        have hA : IsOpen ((J.support : Set Y₁)ᶜ) := J.support.isClosed.isOpen_compl
        let V : Y.Opens := ⟨s '' ((J.support : Set Y₁)ᶜ ∩ s ⁻¹ᵁ U), isOpen_image s hA⟩
        have hVU : V ≤ U := by
          rintro _ ⟨x, ⟨-, hx⟩, rfl⟩; exact hx
        have hyV : y ∈ V := ⟨y', ⟨hJ, hy'U⟩, hy'⟩
        refine ⟨V, hyV, ?_⟩
        have : IsIso (s ∣_ V) := isIso_restrict_of_le s hVU
        have hπ : IsIso (π ∣_ (s ⁻¹ᵁ V)) := by
          refine Principalise.isIso_restrict_of_blowup h₃ _ ?_
          intro x hx hxJ
          have hxU : x ∈ s ⁻¹ᵁ U := hVU hx
          obtain ⟨w, ⟨hwA, hwU⟩, hw⟩ := (hx : s x ∈ V)
          exact hwA (injOn s hwU hxU hw ▸ hxJ)
        rw [morphismRestrict_comp]
        exact IsIso.comp_isIso' hπ this
    · right; exact hr
