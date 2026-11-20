import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfTensorInj
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBcrisRegularOfTensorInj.lean&line=136#L136)
-/
theorem _root_.GlobalTheory.T.bcris_regular_of_tensorInj : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.TensorInj → C.Regular := by
  first | exact @GlobalTheory.MemLoc.regular_of_tensorInj | exact GlobalTheory.MemLoc.regular_of_tensorInj | (intros; apply GlobalTheory.MemLoc.regular_of_tensorInj <;> assumption)
