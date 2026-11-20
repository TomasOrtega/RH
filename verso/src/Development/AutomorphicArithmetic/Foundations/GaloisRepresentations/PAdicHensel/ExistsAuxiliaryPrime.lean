import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.SetupBasicHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNormHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PAuxPrime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PArithK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PScOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PRootAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PStdForm

open UpperTheory.Gal.W2.Seed

namespace UpperTheory.Gal.G1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_auxiliary_prime : AuxiliaryInertOddPrime := exists_auxiliary_prime_cmDatum
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ArithK_holds : ArithK := pArithK BarEx_holds QuadEx_holds CEx_holds UnitMod_holds CodiffGen_holds CodiffUnit_holds IdemEx_holds RealGen_holds PosGen_holds DeltaEx_holds PerfOf_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ScOf_holds : ScOf := pScOf SetupBasic_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RootAt_holds : RootAt := pRootAt

end UpperTheory.Gal.G1
