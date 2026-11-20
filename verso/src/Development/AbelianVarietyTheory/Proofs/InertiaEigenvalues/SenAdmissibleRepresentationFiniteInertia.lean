import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenFiniteOfNoTower
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfMemInertia

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

/- English proof (translation)
The claim follows from `GlobalTheory.PMon.Ram.senFinite_of_noTower GlobalTheory.PMon.Ram.noTower`.
-/
theorem senFinite : SenFinite := GlobalTheory.PMon.Ram.senFinite_of_noTower GlobalTheory.PMon.Ram.noTower

end GlobalTheory.PMon
