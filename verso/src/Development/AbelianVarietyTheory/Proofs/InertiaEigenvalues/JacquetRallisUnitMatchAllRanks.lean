import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchOfWeilRepQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationQuadraticFieldExistsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

/- English proof (translation)
The claim follows from `GlobalTheory.T.jacquetRallisUnitMatch_of_weilRep_quadratic GlobalTheory.T.weilRepresentation_quadraticField_exists`.
-/
theorem unitMatch_all : ∀ r, UnitMatch r :=
  GlobalTheory.T.jacquetRallisUnitMatch_of_weilRep_quadratic GlobalTheory.T.weilRepresentation_quadraticField_exists

end GlobalTheory.JR
