import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in

/- English proof (translation)
Use `ext_of_isAffine ?_` and prove the remaining obligations. Use extensionality with `a`. Take `⟨b, hb⟩` from `hs (g.appTop.hom a)`. Establish `hεp : ε.appTop.hom (p.appTop.hom b) = b`. Rewrite using `[← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, h]`.

Simplify using the standard rewrite rules. Simplify using `only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]`. Rewrite using `[← hb, hεp]`.
-/
theorem _root_.GlobalTheory.eq_comp_section_of_surjective_appTop {X T Y : Scheme.{0}} [IsAffine Y] (p : X ⟶ T)
    (ε : T ⟶ X) (g : X ⟶ Y) (h : ε ≫ p = 𝟙 T) (hs : Function.Surjective p.appTop.hom) :
    g = p ≫ ε ≫ g := by
  refine ext_of_isAffine ?_
  ext a
  obtain ⟨b, hb⟩ := hs (g.appTop.hom a)
  have hεp : ε.appTop.hom (p.appTop.hom b) = b := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, h]
    simp
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [← hb, hεp]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in

/- English proof (translation)
Introduce `X T Y p ε g h hp hsurj t y hfib`. Take `⟨W, hW, hyW, -⟩` from `exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial`. Establish `hZ : IsClosed (p '' (g ⁻¹ᵁ W : Set X)ᶜ)` using `p.isClosedMap _ (g ⁻¹ᵁ W).isOpen.isClosed_compl`. Set `V : T.Opens` to `⟨(p '' (g ⁻¹ᵁ W : Set X)ᶜ)ᶜ, hZ.isOpen_compl⟩`. Establish `htV : t ∈ V`.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `hx (show g x ∈ W from (hfib x rfl).symm ▸ hyW)`. Establish `hsub : p ⁻¹ᵁ V ≤ g ⁻¹ᵁ W`. Introduce `x hx`. Assume the negation of the conclusion as `hxW`.

Conclude with `hx ⟨x, hxW, rfl⟩`. Establish `hεV : V ≤ ε ⁻¹ᵁ (p ⁻¹ᵁ V)`. Introduce `s hs`. Express the relevant statement in the definitionally equal form `p (ε s) ∈ V`. Rewrite using `[← Scheme.Hom.comp_apply, h]`.

Conclude with `hs`. Use `haveI : IsAffine W := hW`. Use `⟨V, htV, ?_⟩` and prove the remaining obligations. Establish `hsec : ε.resLE (p ⁻¹ᵁ V) V hεV ≫ p ∣_ V = 𝟙 V.toScheme`. Rewrite using `[← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, h]`.

Simplify using the standard rewrite rules. Establish `hsV : Function.Surjective (p ∣_ V).appTop.hom`. Rewrite using `[morphismRestrict_appTop]`. Establish `hiso` using `ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p V ⊤)).op)`. Conclude with `hiso.2.comp (hsurj (V.ι ''ᵁ ⊤))`.

Establish `key` using `congrArg (· ≫ W.ι) (_root_.GlobalTheory.eq_comp_section_of_surjective_appTop (p ∣_ V) (ε.resLE (p ⁻¹ᵁ V) V hεV) (g.resLE W (p ⁻¹ᵁ V) hsub) hsec hsV)`. Simplify using `only [Category.assoc, Scheme.Hom.resLE_comp_ι] at key`. Rewrite using `[key, Scheme.Hom.resLE_comp_ι_assoc, ← Category.assoc (p ∣_ V), morphismRestrict_ι, Category.assoc]`.
-/
theorem _root_.GlobalTheory.local_rigidity : ∀ (X T Y : Scheme.{0}) (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y), ε ≫ p = 𝟙 T → UniversallyClosed p → (∀ V : T.Opens, Function.Surjective (p.app V).hom) → ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) → ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g := by
  intro X T Y p ε g h hp hsurj t y hfib
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  have hZ : IsClosed (p '' (g ⁻¹ᵁ W : Set X)ᶜ) :=
    p.isClosedMap _ (g ⁻¹ᵁ W).isOpen.isClosed_compl
  let V : T.Opens := ⟨(p '' (g ⁻¹ᵁ W : Set X)ᶜ)ᶜ, hZ.isOpen_compl⟩
  have htV : t ∈ V := by
    rintro ⟨x, hx, rfl⟩
    exact hx (show g x ∈ W from (hfib x rfl).symm ▸ hyW)
  have hsub : p ⁻¹ᵁ V ≤ g ⁻¹ᵁ W := by
    intro x hx
    by_contra hxW
    exact hx ⟨x, hxW, rfl⟩
  have hεV : V ≤ ε ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    intro s hs
    change p (ε s) ∈ V
    rw [← Scheme.Hom.comp_apply, h]
    exact hs
  haveI : IsAffine W := hW
  refine ⟨V, htV, ?_⟩
  have hsec : ε.resLE (p ⁻¹ᵁ V) V hεV ≫ p ∣_ V = 𝟙 V.toScheme := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, h]
    simp
  have hsV : Function.Surjective (p ∣_ V).appTop.hom := by
    rw [morphismRestrict_appTop]
    have hiso := ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p V ⊤)).op)
    exact hiso.2.comp (hsurj (V.ι ''ᵁ ⊤))
  have key := congrArg (· ≫ W.ι)
    (_root_.GlobalTheory.eq_comp_section_of_surjective_appTop (p ∣_ V) (ε.resLE (p ⁻¹ᵁ V) V hεV)
      (g.resLE W (p ⁻¹ᵁ V) hsub) hsec hsV)
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι] at key
  rw [key, Scheme.Hom.resLE_comp_ι_assoc, ← Category.assoc (p ∣_ V), morphismRestrict_ι,
    Category.assoc]

end GlobalTheory
