import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialCohomologyVanishingStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

/- English proof (translation)
The claim follows from `GlobalTheory.T.etale_cohomology_locally_acyclic`.
-/
theorem UpperTheory.Cb.etale_cohomology_locally_acyclic :
    GlobalTheory.EtC.C5 :=
  GlobalTheory.T.etale_cohomology_locally_acyclic
