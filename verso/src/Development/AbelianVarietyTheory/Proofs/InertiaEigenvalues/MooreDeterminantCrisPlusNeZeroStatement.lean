import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MooreDeterminantCrisPlusNeZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMon.moore_statement` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMooreDeterminantCrisPlusNeZero.lean&line=154#L154)
-/
theorem _root_.GlobalTheory.T.mooreDeterminant_crisPlus_ne_zero : Moore := by
  first | exact @GlobalTheory.PMon.moore_statement | exact GlobalTheory.PMon.moore_statement | (intros; apply GlobalTheory.PMon.moore_statement <;> assumption)
