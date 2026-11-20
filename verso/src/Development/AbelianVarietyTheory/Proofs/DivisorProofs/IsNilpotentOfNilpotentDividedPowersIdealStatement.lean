import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfNilpotentDividedPowersIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsNilpotentOfNilpotentDividedPowersIdeal.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.isNilpotent_of_nilpotentDividedPowers_ideal : ∀ {D : Type} [CommRing D] [Algebra ℂ D] {J : Ideal D} (dl : DividedPowers J), IsNilDP dl → IsNilpotent J := by
  first | exact @GlobalTheory.AnPer.isNilpotent_of_isDPNilpotent | exact GlobalTheory.AnPer.isNilpotent_of_isDPNilpotent | (intros; apply GlobalTheory.AnPer.isNilpotent_of_isDPNilpotent <;> assumption)
