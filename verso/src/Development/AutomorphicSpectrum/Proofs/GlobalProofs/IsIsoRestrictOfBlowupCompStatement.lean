import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIsoRestrictOfBlowupComp
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Principalise.isIso_restrict_of_isIso_restrict_comp_blowup` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FIsIsoRestrictOfBlowupComp.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.isIso_restrict_of_blowup_comp : ∀ {X X₁ X₂ : Scheme.{0}} (s : X₁ ⟶ X) (π : X₂ ⟶ X₁) (Z : X₁.IdealSheafData) (V : X.Opens), IsIntegral X₁ → IsSeparated s → FinalTheorems.Blowup π Z → Nonempty X₂ → IsIso ((π ≫ s) ∣_ V) → IsIso (s ∣_ V) ∧ IsIso (π ∣_ (s ⁻¹ᵁ V)) := by
  first | exact @GlobalTheory.CompanionTheory.Principalise.isIso_restrict_of_isIso_restrict_comp_blowup | exact GlobalTheory.CompanionTheory.Principalise.isIso_restrict_of_isIso_restrict_comp_blowup | (intros; apply GlobalTheory.CompanionTheory.Principalise.isIso_restrict_of_isIso_restrict_comp_blowup <;> assumption)
