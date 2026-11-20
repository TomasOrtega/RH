import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosureTensorBcrisToBdRInjective
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MemLoc.TensorInj.tensorInj` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAlgClosureTensorBcrisToBdRInjective.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective : ∀ (l : ℕ) [Fact l.Prime] (c : Core l), c.TensorInj := by
  first | exact @GlobalTheory.MemLoc.TensorInj.tensorInj | exact GlobalTheory.MemLoc.TensorInj.tensorInj | (intros; apply GlobalTheory.MemLoc.TensorInj.tensorInj <;> assumption)
