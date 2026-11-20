import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSpaceContainsDiscreteSeriesTensor
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFockSpaceContainsDiscreteSeriesTensor.lean&line=311#L311)
-/
theorem _root_.GlobalTheory.T.fockSpace_contains_discreteSeriesTensor : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → DiscreteSeriesPositivity X → admQ5 X → CoverHaarIntegration X → admQ7 → admQ8 → ArchimedeanRallisFirst X → ArchimedeanRallisSecond X := by
  first | exact @GlobalTheory.FockTensor.fock_contains_tensor | exact GlobalTheory.FockTensor.fock_contains_tensor | (intros; apply GlobalTheory.FockTensor.fock_contains_tensor <;> assumption)
