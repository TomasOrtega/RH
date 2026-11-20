import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartierAtOfNotMemSupport
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierIffForallCartAt
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FCartierAtOfNotMemSupport.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.cartier_at_of_not_mem_support : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (x : X), x ∉ J.support → CartAt J x := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support <;> assumption)
