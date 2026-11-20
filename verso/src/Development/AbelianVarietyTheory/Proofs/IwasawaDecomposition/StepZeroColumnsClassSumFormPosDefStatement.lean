import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroColumnsClassSumFormPosDef
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FStepZeroColumnsClassSumFormPosDef.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.stepZeroColumns_classSumForm_posDef : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok), SpectralModel.ColsPos (I.cols l) := by
  first | exact @GlobalTheory.Mem.Df.cols_pos | exact GlobalTheory.Mem.Df.cols_pos | (intros; apply GlobalTheory.Mem.Df.cols_pos <;> assumption)
