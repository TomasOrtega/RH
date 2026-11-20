import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierRestrictIffCartierAt
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierIffForallCartAt
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FEffCartierRestrictIffCartierAt.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.effCartier_restrict_iff_cartier_at : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (O : X.Opens), FinalTheorems.EffCartier (J.comap O.ι) ↔ ∀ x ∈ O, CartAt J x := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff <;> assumption)
