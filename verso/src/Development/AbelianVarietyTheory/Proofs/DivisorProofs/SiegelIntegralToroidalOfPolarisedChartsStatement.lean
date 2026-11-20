import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelIntegralToroidalOfPolarisedCharts
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSiegelIntegralToroidalOfPolarisedCharts.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.siegelIntegralToroidal_of_polarisedCharts : (∀ g : ℕ, ∃ φ : InvFun ℤ, IsPolFan (id : ℤ → ℤ) g φ ∧ NoSelfInt (id : ℤ → ℤ) g φ) → GlobalTheory.Published.SiegelToroidalPolCharts → GlobalTheory.Published.SiegelToroidalIntegral := by
  first | exact @GlobalTheory.PolDeg.siegelToroidalIntegral_of_polCharts | exact GlobalTheory.PolDeg.siegelToroidalIntegral_of_polCharts | (intros; apply GlobalTheory.PolDeg.siegelToroidalIntegral_of_polCharts <;> assumption)
