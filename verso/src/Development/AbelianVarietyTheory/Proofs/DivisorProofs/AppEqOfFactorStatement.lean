import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppEqOfFactor
import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAppEqOfFactor.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.app_opensRange_eq_appLE_comp_of_factor : ∀ {X Y : Scheme.{0}} {A : CommRingCat.{0}} (κ : Spec A ⟶ Y) [IsOpenImmersion κ] (j : X ⟶ Y) (O : X.Opens) (q : A ⟶ Γ(X, O)) (hO : j ⁻¹ᵁ κ.opensRange = O), O.ι ≫ j = (O.toSpecΓ ≫ Spec.map q) ≫ κ → j.app κ.opensRange ≫ X.presheaf.map (homOfLE hO.ge).op = κ.appLE κ.opensRange ⊤ (fun x _ ↦ ⟨x, rfl⟩) ≫ (Scheme.ΓSpecIso A).hom ≫ q := by
  first | exact @GlobalTheory.SectionsPinch.app_eq_of_factor | exact GlobalTheory.SectionsPinch.app_eq_of_factor | (intros; apply GlobalTheory.SectionsPinch.app_eq_of_factor; all_goals assumption)
