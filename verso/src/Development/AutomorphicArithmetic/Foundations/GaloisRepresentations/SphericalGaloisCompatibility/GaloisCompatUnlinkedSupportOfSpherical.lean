import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.GaloisCompatUnlinkedSupportOfSpherical
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.InputsOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.CharLiftPrimeHolds

namespace UpperTheory.Gal.ToralGalois

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem inq_holds : Inq := ⟨UpperTheory.Gal.Int.Inp.inp_holds, UpperTheory.Gal.GamX.charLiftPrime_holds⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem galoisCompat_unlinkedSupport_of_spherical : GlobalTheory.RoadU.CoreAll → GlobalTheory.DeRhamOfPlainTorus.R1 := GalTw.GlobalTheory.DeRhamOfPlainTorus.galoisCompat_unlinkedSupport_of_spherical inq_holds

end UpperTheory.Gal.ToralGalois
