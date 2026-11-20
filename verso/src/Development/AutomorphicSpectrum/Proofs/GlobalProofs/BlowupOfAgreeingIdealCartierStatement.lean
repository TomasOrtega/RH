import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlowupOfAgreeingIdealCartier
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue.blowup_of_eq_on_open` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FBlowupOfAgreeingIdealCartier.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.blowup_of_agreeing_ideal_cartier : ∀ {X₁ X₂ : Scheme.{0}} (π : X₂ ⟶ X₁) (Z Z' : X₁.IdealSheafData) (O₁ O₂ : X₁.Opens), FinalTheorems.Blowup π Z → O₁ ⊔ O₂ = ⊤ → Z'.comap O₁.ι = Z.comap O₁.ι → (∀ x ∈ O₂, x ∉ Z'.support) → FinalTheorems.EffCartier (Z.comap O₂.ι) → FinalTheorems.Blowup π Z' := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue.blowup_of_eq_on_open | exact GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue.blowup_of_eq_on_open | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue.blowup_of_eq_on_open <;> assumption)
