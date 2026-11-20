import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.SeenShapeHolds

/- English proof (translation)
The claim follows from `UpperTheory.Gal.W2.Seed.memFn_holds`.
-/
theorem UpperTheory.Gal.Spc.memFn :
    UpperTheory.Gal.Spc.MemFn :=
  UpperTheory.Gal.W2.Seed.memFn_holds
