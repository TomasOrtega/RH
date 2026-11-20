import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.SeenShapeHolds

/- English proof (translation)
The claim follows from `UpperTheory.Gal.W2.Seed.phiEx_holds`.
-/
theorem UpperTheory.Gal.Spc.phiEx :
    UpperTheory.Gal.Spc.PhiEx :=
  UpperTheory.Gal.W2.Seed.phiEx_holds
