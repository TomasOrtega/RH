import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalRankOneOfLocallyPrincipal
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierIffForallCartAt
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocPrincipalSpan
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.rankAtStalk_cotangent_eq_one` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FConormalRankOneOfLocallyPrincipal.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.conormal_rank_one_of_locally_principal : ∀ {A : Type} [CommRing A] [IsDomain A] (I : Ideal A) [Module.Finite (A ⧸ I) I.Cotangent] [Module.Projective (A ⧸ I) I.Cotangent] (P : PrimeSpectrum (A ⧸ I)), LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I)) → Module.rankAtStalk I.Cotangent P = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.rankAtStalk_cotangent_eq_one | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.rankAtStalk_cotangent_eq_one | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.rankAtStalk_cotangent_eq_one <;> assumption)
