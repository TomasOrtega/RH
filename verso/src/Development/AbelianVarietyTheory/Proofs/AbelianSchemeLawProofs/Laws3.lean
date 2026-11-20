import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

/- English proof (translation)
Assemble the required witnesses or components as `⟨gtBaseChange, CubePf.cubePull⟩`.
-/
theorem laws3 : Laws3 :=
  ⟨gtBaseChange, CubePf.cubePull⟩

end GlobalTheory
