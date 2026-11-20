import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocallyPrincipalOfConormalRankOne
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierIffForallCartAt
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocPrincipalSpan
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FLocallyPrincipalOfConormalRankOne.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.locally_principal_of_conormal_rank_one : ∀ {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] (I : Ideal A) [Module.Finite (A ⧸ I) I.Cotangent] [Module.Projective (A ⧸ I) I.Cotangent] (P : PrimeSpectrum (A ⧸ I)), Module.rankAtStalk I.Cotangent P = 1 → LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one <;> assumption)
