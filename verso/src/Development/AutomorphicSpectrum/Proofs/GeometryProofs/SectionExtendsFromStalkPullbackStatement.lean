import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionExtendsFromStalkPullback
import Mathlib
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FSectionExtendsFromStalkPullback.lean&line=158#L158)
-/
theorem _root_.GlobalTheory.T.section_extends_from_stalk_pullback : ∀ {X Y Z : Scheme.{0}} (π : Y ⟶ X) (p : X) (y₀ : Y), π y₀ = p → ∀ (c : Z ⟶ pullback π (X.fromSpecStalk p)) [IsClosedImmersion c] (s : Γ(Z, ⊤)), ∃ (W : Y.Opens) (f : Γ(Y, W)), y₀ ∈ W ∧ ((c ≫ pullback.fst π (X.fromSpecStalk p)).app W).hom f = Z.presheaf.map (homOfLE (le_top : (c ≫ pullback.fst π (X.fromSpecStalk p)) ⁻¹ᵁ W ≤ ⊤)).op s := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_open_extension | exact GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_open_extension | (intros; apply GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_open_extension <;> assumption)
