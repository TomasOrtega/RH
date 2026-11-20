import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassificationRankOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DSSU.Triv.classS_one_classU_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FClassificationRankOne.lean&line=143#L143)
-/
theorem _root_.GlobalTheory.T.classification_rank_one : (∀ ε : Fin 1 → Bool, ClassS ε) ∧ ClassU 0 := by
  first | exact @GlobalTheory.DSSU.Triv.classS_one_classU_zero | exact GlobalTheory.DSSU.Triv.classS_one_classU_zero | (intros; apply GlobalTheory.DSSU.Triv.classS_one_classU_zero <;> assumption)
