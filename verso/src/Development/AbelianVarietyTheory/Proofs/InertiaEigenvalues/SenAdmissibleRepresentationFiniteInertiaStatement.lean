import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenAdmissibleRepresentationFiniteInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.PMon.senFinite | exact GlobalTheory.PMon.senFinite | (intros; apply GlobalTheory.PMon.senFinite <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.sen_admissible_representation_finite_inertia : SenFinite := by
  first | exact @GlobalTheory.PMon.senFinite | exact GlobalTheory.PMon.senFinite | (intros; apply GlobalTheory.PMon.senFinite <;> assumption)
