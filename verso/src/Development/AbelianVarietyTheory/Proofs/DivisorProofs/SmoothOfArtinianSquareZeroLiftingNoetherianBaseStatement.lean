import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfArtinianSquareZeroLiftingNoetherianBase
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SmoothCrit.smooth_of_artinian_lift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmoothOfArtinianSquareZeroLiftingNoetherianBase.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.smooth_of_artinian_squareZero_lifting_noetherian_base : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), LocallyOfFiniteType s → (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → Smooth s := by
  first | exact @GlobalTheory.SmoothCrit.smooth_of_artinian_lift | exact GlobalTheory.SmoothCrit.smooth_of_artinian_lift | (intros; apply GlobalTheory.SmoothCrit.smooth_of_artinian_lift <;> assumption)
