import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodZeroOfClassPeriodDecompositionAl
import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FAdmissiblePeriodZeroOfClassPeriodDecompositionAl.lean&line=249#L249)
-/
theorem _root_.GlobalTheory.T.admissiblePeriodZero_of_classPeriodDecomposition_all : ∀ D : D7, (∀ u, Formalism.MainNotions.RT.PeriodPointConditions.PerDec0 D u) → Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl D := by
  first | exact @GlobalTheory.PerRed.periodClassSumWeyl_of_forall_perDec0 | exact GlobalTheory.PerRed.periodClassSumWeyl_of_forall_perDec0 | (intros; apply GlobalTheory.PerRed.periodClassSumWeyl_of_forall_perDec0 <;> assumption)
