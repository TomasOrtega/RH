import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.SectionsPinch

/- English proof (translation)
Establish `key : ∀ (f g : O.toScheme ⟶ Y), f = g → ∀ e e', f.appLE κ.opensRange ⊤ e = g.appLE κ.opensRange ⊤ e'`. Introduce and unpack `f g rfl e e'`. Both sides reduce to the same expression. Establish `hle' : ⊤ ≤ (O.ι ≫ j) ⁻¹ᵁ κ.opensRange` using `fun x _ ↦ (hO.ge x.2 : _)`. Rewrite using `[← cancel_mono O.topIso.inv]`.

Establish `lhs : (j.app κ.opensRange ≫ X.presheaf.map (homOfLE hO.ge).op) ≫ O.topIso.inv = (O.ι ≫ j).appLE κ.opensRange ⊤ hle'` using `by show j.appLE κ.opensRange O hO.ge ≫ O.topIso.inv = _`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE O.ι j κ.opensRange O ⊤ hO.ge (fun x _ ↦ x.2)]`. Use `congr 1`. Rewrite using `[Scheme.Opens.topIso_inv]`. Conclude with `(Scheme.Opens.ι_appLE O O ⊤ _).symm`.

Rewrite using `[lhs, key _ _ hfac hle' (hfac ▸ hle')]`. Simplify using `only [Category.assoc]`. Rewrite using `[← Scheme.ΓSpecIso_naturality_assoc, ← Scheme.Opens.toSpecΓ_appTop]`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE O.toSpecΓ (Spec.map q ≫ κ) κ.opensRange ⊤ ⊤ (fun x _ ↦ ⟨_, rfl⟩) le_top, ← Scheme.Hom.appLE_comp_appLE (Spec.map q) κ κ.opensRange ⊤ ⊤ (fun x _ ↦ ⟨x, rfl⟩) le_top, Category.assoc]`. Establish `top : ∀ {P Q : Scheme.{0}} (f : P ⟶ Q) (e : ⊤ ≤ f ⁻¹ᵁ ⊤), f.appLE ⊤ ⊤ e = f.appTop` using `fun f _ ↦ Scheme.Hom.appLE_eq_app (f := f) (U := ⊤)`.

Rewrite using `[← top (Spec.map q) le_top, ← top O.toSpecΓ le_top]`.
-/
theorem app_eq_of_factor {X Y : Scheme.{0}} {A : CommRingCat.{0}} (κ : Spec A ⟶ Y) [IsOpenImmersion κ]
    (j : X ⟶ Y) (O : X.Opens) (q : A ⟶ Γ(X, O)) (hO : j ⁻¹ᵁ κ.opensRange = O)
    (hfac : O.ι ≫ j = (O.toSpecΓ ≫ Spec.map q) ≫ κ) :
    j.app κ.opensRange ≫ X.presheaf.map (homOfLE hO.ge).op =
      κ.appLE κ.opensRange ⊤ (fun x _ ↦ ⟨x, rfl⟩) ≫ (Scheme.ΓSpecIso A).hom ≫ q := by
  have key : ∀ (f g : O.toScheme ⟶ Y), f = g → ∀ e e',
      f.appLE κ.opensRange ⊤ e = g.appLE κ.opensRange ⊤ e' := by
    rintro f g rfl e e'; rfl
  have hle' : ⊤ ≤ (O.ι ≫ j) ⁻¹ᵁ κ.opensRange := fun x _ ↦
    (hO.ge x.2 : _)
  rw [← cancel_mono O.topIso.inv]
  have lhs : (j.app κ.opensRange ≫ X.presheaf.map (homOfLE hO.ge).op) ≫ O.topIso.inv =
      (O.ι ≫ j).appLE κ.opensRange ⊤ hle' := by
    show j.appLE κ.opensRange O hO.ge ≫ O.topIso.inv = _
    rw [← Scheme.Hom.appLE_comp_appLE O.ι j κ.opensRange O ⊤ hO.ge (fun x _ ↦ x.2)]
    congr 1
    rw [Scheme.Opens.topIso_inv]
    exact (Scheme.Opens.ι_appLE O O ⊤ _).symm
  rw [lhs, key _ _ hfac hle' (hfac ▸ hle')]
  simp only [Category.assoc]
  rw [← Scheme.ΓSpecIso_naturality_assoc, ← Scheme.Opens.toSpecΓ_appTop]
  rw [← Scheme.Hom.appLE_comp_appLE O.toSpecΓ (Spec.map q ≫ κ) κ.opensRange ⊤ ⊤
      (fun x _ ↦ ⟨_, rfl⟩) le_top,
    ← Scheme.Hom.appLE_comp_appLE (Spec.map q) κ κ.opensRange ⊤ ⊤ (fun x _ ↦ ⟨x, rfl⟩) le_top,
    Category.assoc]
  have top : ∀ {P Q : Scheme.{0}} (f : P ⟶ Q) (e : ⊤ ≤ f ⁻¹ᵁ ⊤), f.appLE ⊤ ⊤ e = f.appTop :=
    fun f _ ↦ Scheme.Hom.appLE_eq_app (f := f) (U := ⊤)
  rw [← top (Spec.map q) le_top, ← top O.toSpecΓ le_top]

end GlobalTheory.SectionsPinch
