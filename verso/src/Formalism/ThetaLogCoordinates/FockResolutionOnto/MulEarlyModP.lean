import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.GramBoundOfRestrictionOfProj
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.HighestVectorProjection
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.ResSat
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.DerivativeKeepsSpaceHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.OmegaInjectiveHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.MulEarlyLettersModP

namespace Formalism.InvariantFactorPaths.L4.Top

open Formalism.InvariantFactorPaths.L4

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uComm : UComm := raising_comm_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uKeepsLast : UKeepsLast := raising_keeps_last_letter
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uKeepsEarly : UKeepsEarly := raising_keeps_early_letters
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uDeg : UDeg := raising_degree_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem resU : ResU := restriction_raising_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dKeepsX : DKeepsX := derivative_keeps_space_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sl2Inj : Sl2Injective := sl2_injectivity_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eArith : EArith := exponent_arithmetic_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem omegaInj : OmegaInj := omega_injective_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem resOntoKThm : ResOntoKThm := resOntoKThm_of omega_injective_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dpowInt : DpowInt := divided_power_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem modOfY : ModOfY := mod_p_of_conditions
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mulEarlyModP : MulEarlyModP := mul_early_letters_mod_p
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mulLastModP : MulLastModP := mul_last_letter_mod_p
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem divModPOf : DivModPOf := divided_power_mod_p_of

end Formalism.InvariantFactorPaths.L4.Top
