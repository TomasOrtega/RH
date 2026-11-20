import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallySemistableReducibleUnramifiedSplit
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.Red.redStep` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPotentiallySemistableReducibleUnramifiedSplit.lean&line=222#L222)
-/
theorem _root_.GlobalTheory.T.potentially_semistable_reducible_unramified_split : RedStep := by
  first | exact @GlobalTheory.PMon.Red.redStep | exact GlobalTheory.PMon.Red.redStep | (intros; apply GlobalTheory.PMon.Red.redStep <;> assumption)
