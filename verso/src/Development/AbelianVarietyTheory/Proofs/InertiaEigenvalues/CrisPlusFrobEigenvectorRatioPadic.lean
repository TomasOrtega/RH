import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioIntegral

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

/- English proof (translation)
The claim follows from `GlobalTheory.PMon.RatioTransport.ratio_of_acris`.
-/
theorem ratio_holds : Ratio := GlobalTheory.PMon.RatioTransport.ratio_of_acris

end GlobalTheory.PMon

end
