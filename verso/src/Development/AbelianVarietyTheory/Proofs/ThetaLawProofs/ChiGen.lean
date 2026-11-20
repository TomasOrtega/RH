import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FromBlocksMapIntCastMemSymplecticGroup

open ReciprocityTheory.ChartRestriction.G.Key

namespace GlobalTheory.ThetaInversion

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem inversion : Chi.InversionStatement := GlobalTheory.inversionStatement_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem chi : Chi.ChiStatement := Chi.chi_of inversion Chi.spGen

end GlobalTheory.ThetaInversion
