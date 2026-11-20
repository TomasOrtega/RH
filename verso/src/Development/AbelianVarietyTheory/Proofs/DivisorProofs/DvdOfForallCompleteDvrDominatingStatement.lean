import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallCompleteDvrDominating
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Poinc.dvd_of_forall_complete_dvr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDvdOfForallCompleteDvrDominating.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.dvd_of_forall_complete_dvr_dominating : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (f g : R), g ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ ρ : R →+* V, Function.Injective ρ → IsLocalHom ρ → ρ g ∣ ρ f) → g ∣ f := by
  first | exact @GlobalTheory.Poinc.dvd_of_forall_complete_dvr | exact GlobalTheory.Poinc.dvd_of_forall_complete_dvr | (intros; apply GlobalTheory.Poinc.dvd_of_forall_complete_dvr <;> assumption)
