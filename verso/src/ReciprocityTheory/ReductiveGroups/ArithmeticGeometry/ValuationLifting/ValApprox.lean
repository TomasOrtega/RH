import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.LiftSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.ValuationApproximation.Development
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.ValuationApproximation.RhoProjectionAssembly

/- English proof (translation)
The claim follows from `ReciprocityTheory.ChartRestriction.G.Lift.VA.valApprox_of ReciprocityTheory.ChartRestriction.G.Lift.VA.pair_separation ReciprocityTheory.ChartRestriction.G.Lift.VA.large_small_separation ReciprocityTheory.ChartRestriction.G.Lift.VA.near_one_approximation ReciprocityTheory.ChartRe …`.
-/
theorem ReciprocityTheory.ChartRestriction.G.Lift.valuation_approximation : ReciprocityTheory.ChartRestriction.G.Lift.ApproxStatement :=
  ReciprocityTheory.ChartRestriction.G.Lift.VA.valApprox_of ReciprocityTheory.ChartRestriction.G.Lift.VA.pair_separation ReciprocityTheory.ChartRestriction.G.Lift.VA.large_small_separation ReciprocityTheory.ChartRestriction.G.Lift.VA.near_one_approximation ReciprocityTheory.ChartRestriction.G.Lift.VA.rho_projection_assembly
