import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenAdmissibleRepresentationFiniteInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.senFinite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FSenAdmissibleRepresentationFiniteInertia.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.sen_admissible_representation_finite_inertia : SenFinite := by
  first | exact @GlobalTheory.PMon.senFinite | exact GlobalTheory.PMon.senFinite | (intros; apply GlobalTheory.PMon.senFinite <;> assumption)
