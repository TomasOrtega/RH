import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVStatement
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem semiAbelian_model_determined_by_generic_fibre : ExtVStatement :=
  GlobalTheory.ModelUniqueChecks.extV_holds

end GlobalTheory
