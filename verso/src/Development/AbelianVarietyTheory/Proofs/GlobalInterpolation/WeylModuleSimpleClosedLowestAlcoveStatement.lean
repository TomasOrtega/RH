import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylModuleSimpleClosedLowestAlcove
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Alc.inducedSimpleLowestAlcove | exact GlobalTheory.Alc.inducedSimpleLowestAlcove | (intros; apply GlobalTheory.Alc.inducedSimpleLowestAlcove <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.weylModule_simple_closedLowestAlcove : GlobalTheory.Published.InducedSimpleLowestAlcove := by
  first | exact @GlobalTheory.Alc.inducedSimpleLowestAlcove | exact GlobalTheory.Alc.inducedSimpleLowestAlcove | (intros; apply GlobalTheory.Alc.inducedSimpleLowestAlcove <;> assumption)
