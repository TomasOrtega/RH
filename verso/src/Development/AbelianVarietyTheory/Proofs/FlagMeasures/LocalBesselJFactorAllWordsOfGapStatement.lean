import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalBesselJFactorAllWordsOfGap
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JFactTie.jFactN_all` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLocalBesselJFactorAllWordsOfGap.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.localBesselJFactor_all_words_of_gap : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → JFactN hI C hB u u' := by
  first | exact @GlobalTheory.JFactTie.jFactN_all | exact GlobalTheory.JFactTie.jFactN_all | (intros; apply GlobalTheory.JFactTie.jFactN_all <;> assumption)
