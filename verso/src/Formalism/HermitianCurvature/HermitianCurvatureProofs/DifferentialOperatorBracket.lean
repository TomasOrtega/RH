import Formalism.HermitianCurvature.HermitianCurvatureProofs.IrreducibleCapelliModules
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupGeneratedByExp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieListProducts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankFour
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFrameTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameExtension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProductIntervalFrames
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialDecompositionSpectralOfBranching

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

/- English proof (translation)
The claim follows from `qr_dOpLin_of trotter_product_formula trotter_product_matrices representation_exp`.
-/
theorem differential_operator_linear : Qr.DOpLin := qr_dOpLin_of trotter_product_formula trotter_product_matrices representation_exp

/- English proof (translation)
The claim follows from `qr_dOpBracket_of representation_exp differential_operator_linear differential_operator_adjoint`.
-/
theorem differential_operator_bracket : Qr.DOpBracket := qr_dOpBracket_of representation_exp differential_operator_linear differential_operator_adjoint

/- English proof (translation)
The claim follows from `qr_ecLie_of differential_operator_linear differential_operator_bracket`.
-/
theorem elementary_lie_elements : Qr.EcLie := qr_ecLie_of differential_operator_linear differential_operator_bracket

/- English proof (translation)
The claim follows from `qr_frameGl_of elementary_lie_elements`.
-/
theorem frame_general_linear : Qr.FrameGl := qr_frameGl_of elementary_lie_elements

/- English proof (translation)
The claim follows from `qr_lieStab_of exp_generates representation_exp elementary_lie_elements`.
-/
theorem lie_stabilizer : Qr.LieStab := qr_lieStab_of exp_generates representation_exp elementary_lie_elements

/- English proof (translation)
The claim follows from `qr_frameChange_of elementary_lie_elements frame_general_linear`.
-/
theorem qr_frameChange_proof : Qr.FrameChange := qr_frameChange_of elementary_lie_elements frame_general_linear

/- English proof (translation)
The claim follows from `qr_branchingK_of branching_algebraic frame_general_linear lie_stabilizer stabilizer_lie_algebra qr_frameChange_proof exists_frame_two`.
-/
theorem branching_compact : Qr.BranchingK :=
  qr_branchingK_of branching_algebraic frame_general_linear lie_stabilizer stabilizer_lie_algebra qr_frameChange_proof
    exists_frame_two

/- English proof (translation)
The claim follows from `qr_branching_of branching_compact`.
-/
theorem branching_proof : Branching := qr_branching_of branching_compact

/- English proof (translation)
The claim follows from `radialDecompositionSpectral_of_branching branching_proof`.
-/
theorem spectral_two_by_two : RadialDecompositionSpectral := radialDecompositionSpectral_of_branching branching_proof

end Formalism.FourierDecayAlt.P
