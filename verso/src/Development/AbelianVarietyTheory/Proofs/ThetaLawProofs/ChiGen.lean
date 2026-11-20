import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FromBlocksMapIntCastMemSymplecticGroup

open ReciprocityTheory.ChartRestriction.G.Key

namespace GlobalTheory.ThetaInversion

/- English proof (translation)
The claim follows from `GlobalTheory.inversionStatement_holds`.
-/
theorem inversion : Chi.InversionStatement := GlobalTheory.inversionStatement_holds

/- English proof (translation)
The claim follows from `Chi.chi_of inversion Chi.spGen`.
-/
theorem chi : Chi.ChiStatement := Chi.chi_of inversion Chi.spGen

end GlobalTheory.ThetaInversion
