import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroFrobVectorResidueZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_nonzero_frobVector_residue_zero`.
-/
theorem exII_holds : ExII := GlobalTheory.T.exists_nonzero_frobVector_residue_zero

end GlobalTheory.PMon
