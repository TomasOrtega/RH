import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedOfSmoothOverFieldStatement
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
The claim follows from `GlobalTheory.T.isReduced_of_smooth_over_field'`.
-/
theorem UpperTheory.Gal.crystallineComparison.smoothRed_of :
    SmoothReduced :=
  GlobalTheory.T.isReduced_of_smooth_over_field'
