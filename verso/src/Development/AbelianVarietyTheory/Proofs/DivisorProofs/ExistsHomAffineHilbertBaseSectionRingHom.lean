import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

/- English proof (translation)
Use extensionality with `a`. Establish `e : Z.toSpecΓ.appLE ⊤ ⊤ (by simp) = Z.toSpecΓ.appTop` using `(Scheme.Hom.app_eq_appLE _).symm`. Simplify using `only [secAlg, RingHom.comp_apply, e, Scheme.toSpecΓ_appTop]`. Simplify using the standard rewrite rules.
-/
theorem secAlg_toSpecΓ_top (Z : Scheme.{0}) :
    secAlg Γ(Z, ⊤) Z.toSpecΓ ⊤ = RingHom.id _ := by
  ext a
  have e : Z.toSpecΓ.appLE ⊤ ⊤ (by simp) = Z.toSpecΓ.appTop := (Scheme.Hom.app_eq_appLE _).symm
  simp only [secAlg, RingHom.comp_apply, e, Scheme.toSpecΓ_appTop]
  simp

/- English proof (translation)
Use `⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom Φ), ?_⟩` and prove the remaining obligations. Rewrite using `[secAlg_comp, secAlg_toSpecΓ_top]`. Both sides reduce to the same expression.
-/
theorem exists_hom_secAlg_top (Z : Scheme.{0}) (C : Type) [CommRing C] (Φ : C →+* Γ(Z, ⊤)) :
    ∃ h : Z ⟶ Spec (CommRingCat.of C), GlobalTheory.HilbAff.secAlg C h ⊤ = Φ := by
  refine ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom Φ), ?_⟩
  rw [secAlg_comp, secAlg_toSpecΓ_top]
  rfl

end GlobalTheory.HilbAff
