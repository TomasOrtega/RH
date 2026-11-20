import Formalism.HermitianCurvature.HermitianCurvatureProofs.CommonEigenvectors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HighestWeightPolynomials
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliAbstractCharacter
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StarSumLemmas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BorderedDeterminants
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BranchingSystems
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ClosureOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeightMonotonicity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StrictBoxOrder

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

/- English proof (translation)
The claim follows from `qr_capSing_of singular_dominant exists_singular_maximal_vector`.
-/
theorem capelli_singular : Qr.CapSing := qr_capSing_of singular_dominant exists_singular_maximal_vector

/- English proof (translation)
The claim follows from `qr_topWeightSing_of exists_singular_maximal_vector capelli_singular`.
-/
theorem top_weight_singular : Qr.TopWeightSing := qr_topWeightSing_of exists_singular_maximal_vector capelli_singular

/- English proof (translation)
The claim follows from `qr_vecDown_of quantum_minor_polynomial polynomial_vanishing`.
-/
theorem vector_descent : Qr.VecDown := qr_vecDown_of quantum_minor_polynomial polynomial_vanishing

/- English proof (translation)
The claim follows from `qr_raiseNZ_of covariant_raising`.
-/
theorem raising_nonzero : Qr.RaiseNZ := qr_raiseNZ_of covariant_raising

/- English proof (translation)
The claim follows from `qr_lowerNZ_of vector_descent`.
-/
theorem lowering_nonzero : Qr.LowerNZ := qr_lowerNZ_of vector_descent

/- English proof (translation)
The claim follows from `qr_decomp_of exists_singular_maximal_vector capelli_singular capelli_stabilizer submodule_relations covariant_raising vector_descent raising_nonzero lowering_nonzero`.
-/
theorem branching_decomposition : Qr.Decomp :=
  qr_decomp_of exists_singular_maximal_vector capelli_singular capelli_stabilizer submodule_relations covariant_raising vector_descent
    raising_nonzero lowering_nonzero

/- English proof (translation)
The claim follows from `qr_multOne_of exists_singular_maximal_vector dual_minor span_singular_vectors`.
-/
theorem multiplicity_one : Qr.MultOne := qr_multOne_of exists_singular_maximal_vector dual_minor span_singular_vectors

/- English proof (translation)
The claim follows from `qr_irredCap_of exists_singular_maximal_vector capelli_singular capelli_stabilizer submodule_relations top_weight_singular dual_minor span_top_vectors multiplicity_one branching_decomposition capelli_independence`.
-/
theorem irreducible_capelli_modules : Qr.IrredCap :=
  qr_irredCap_of exists_singular_maximal_vector capelli_singular capelli_stabilizer submodule_relations top_weight_singular
    dual_minor span_top_vectors multiplicity_one branching_decomposition capelli_independence

/- English proof (translation)
The claim follows from `qr_branchingAlg_of branching_decomposition capelli_independence irreducible_capelli_modules`.
-/
theorem branching_algebraic : Qr.BranchingAlg := qr_branchingAlg_of branching_decomposition capelli_independence irreducible_capelli_modules

end Formalism.FourierDecayAlt.P
