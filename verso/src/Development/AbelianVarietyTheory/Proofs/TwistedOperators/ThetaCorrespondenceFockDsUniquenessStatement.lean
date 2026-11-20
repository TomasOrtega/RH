import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceFockDsUniqueness
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FThetaCorrespondenceFockDsUniqueness.lean&line=424#L424)
-/
theorem _root_.GlobalTheory.T.theta_correspondence_fock_ds_uniqueness : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → admQ5 X → admQ7 → admQ8 → ArchimedeanRallisFirst X → ArchimedeanRallisSecond X → ArchimedeanRallisUpDownLine X := by
  first | exact @GlobalTheory.ThetaUnique.theta_unique | exact GlobalTheory.ThetaUnique.theta_unique | (intros; apply GlobalTheory.ThetaUnique.theta_unique <;> assumption)
