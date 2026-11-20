import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsClosedCartierLocusSupport
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierIffForallCartAt
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FIsClosedCartierLocusSupport.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.isClosed_cartier_locus_support : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData), Smooth g → IsIntegral X → Smooth (Z.subschemeι ≫ g) → IsClosed {x : X | x ∈ Z.support ∧ CartAt Z x} ∧ IsClosed {x : X | x ∈ Z.support ∧ ¬ CartAt Z x} := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt <;> assumption)
