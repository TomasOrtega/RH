import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.GramBoundOfRestrictionOfProj
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.HighestVectorProjection
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.ResSat
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.DerivativeKeepsSpaceHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.OmegaInjectiveHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.MulEarlyLettersModP

namespace Formalism.InvariantFactorPaths.L4.Top

open Formalism.InvariantFactorPaths.L4

/- English proof (translation)
The claim follows from `raising_comm_holds`.
-/
theorem uComm : UComm := raising_comm_holds
/- English proof (translation)
The claim follows from `raising_keeps_last_letter`.
-/
theorem uKeepsLast : UKeepsLast := raising_keeps_last_letter
/- English proof (translation)
The claim follows from `raising_keeps_early_letters`.
-/
theorem uKeepsEarly : UKeepsEarly := raising_keeps_early_letters
/- English proof (translation)
The claim follows from `raising_degree_holds`.
-/
theorem uDeg : UDeg := raising_degree_holds
/- English proof (translation)
The claim follows from `restriction_raising_holds`.
-/
theorem resU : ResU := restriction_raising_holds
/- English proof (translation)
The claim follows from `derivative_keeps_space_holds`.
-/
theorem dKeepsX : DKeepsX := derivative_keeps_space_holds
/- English proof (translation)
The claim follows from `sl2_injectivity_holds`.
-/
theorem sl2Inj : Sl2Injective := sl2_injectivity_holds
/- English proof (translation)
The claim follows from `exponent_arithmetic_holds`.
-/
theorem eArith : EArith := exponent_arithmetic_holds
/- English proof (translation)
The claim follows from `omega_injective_holds`.
-/
theorem omegaInj : OmegaInj := omega_injective_holds
/- English proof (translation)
The claim follows from `resOntoKThm_of omega_injective_holds`.
-/
theorem resOntoKThm : ResOntoKThm := resOntoKThm_of omega_injective_holds
/- English proof (translation)
The claim follows from `divided_power_integral`.
-/
theorem dpowInt : DpowInt := divided_power_integral
/- English proof (translation)
The claim follows from `mod_p_of_conditions`.
-/
theorem modOfY : ModOfY := mod_p_of_conditions
/- English proof (translation)
The claim follows from `mul_early_letters_mod_p`.
-/
theorem mulEarlyModP : MulEarlyModP := mul_early_letters_mod_p
/- English proof (translation)
The claim follows from `mul_last_letter_mod_p`.
-/
theorem mulLastModP : MulLastModP := mul_last_letter_mod_p
/- English proof (translation)
The claim follows from `divided_power_mod_p_of`.
-/
theorem divModPOf : DivModPOf := divided_power_mod_p_of

end Formalism.InvariantFactorPaths.L4.Top
