import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeUnipotentIntegralNormalisedHaar
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovNFormulaPf.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCovolumeUnipotentIntegralNormalisedHaar.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.covolume_unipotentIntegral_normalisedHaar : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula := by
  first | exact @GlobalTheory.CovNFormulaPf.main | exact GlobalTheory.CovNFormulaPf.main | (intros; apply GlobalTheory.CovNFormulaPf.main <;> assumption)
