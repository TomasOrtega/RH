import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIntegralBlowupOfSmooth
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FIsIntegralBlowupOfSmooth.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.isIntegral_blowup_of_smooth : ∀ {k : Type} [Field k] {X₁ X₂ : Scheme.{0}} (g : X₁ ⟶ Sp k) (Z : X₁.IdealSheafData) (π : X₂ ⟶ X₁), IsIntegral X₁ → FinalTheorems.Blowup π Z → Smooth (π ≫ g) → Nonempty X₂ → IsIntegral X₂ := by
  first | exact @GlobalTheory.CompanionTheory.BlowupIntegral.isIntegral_of_smooth_blowup | exact GlobalTheory.CompanionTheory.BlowupIntegral.isIntegral_of_smooth_blowup | (intros; apply GlobalTheory.CompanionTheory.BlowupIntegral.isIntegral_of_smooth_blowup <;> assumption)
