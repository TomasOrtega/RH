import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeHomExtOfJointlyInjective
import Mathlib
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.scheme_hom_ext_of_jointly_injective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchemeHomExtOfJointlyInjective.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.scheme_hom_ext_of_jointly_surjective_of_app_injective : ∀ (Z Z₁ Z₂ X : Scheme.{0}) (e₁ : Z₁ ⟶ Z) (e₂ : Z₂ ⟶ Z), (∀ z : Z, (∃ z₁, e₁ z₁ = z) ∨ ∃ z₂, e₂ z₂ = z) → (∀ (W : Z.Opens) (a b : Γ(Z, W)), e₁.app W a = e₁.app W b → e₂.app W a = e₂.app W b → a = b) → ∀ f g : Z ⟶ X, e₁ ≫ f = e₁ ≫ g → e₂ ≫ f = e₂ ≫ g → f = g := by
  first | exact @GlobalTheory.scheme_hom_ext_of_jointly_injective | exact GlobalTheory.scheme_hom_ext_of_jointly_injective | (intros; apply GlobalTheory.scheme_hom_ext_of_jointly_injective <;> assumption)
