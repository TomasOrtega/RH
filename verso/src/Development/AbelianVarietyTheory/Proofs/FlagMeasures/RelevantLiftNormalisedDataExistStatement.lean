import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantLiftNormalisedDataExist
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRelevantLiftNormalisedDataExist.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.relevantLift_normalisedData_exist : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), PinAll (Y := Y) u u' := by
  first | exact @GlobalTheory.pinAll_all | exact GlobalTheory.pinAll_all | (intros; apply GlobalTheory.pinAll_all <;> assumption)
