import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKtypeCoefficientExplicitPowerDecay
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SepReal.decPow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FLowestKtypeCoefficientExplicitPowerDecay.lean&line=118#L118)
-/
theorem _root_.GlobalTheory.T.lowest_Ktype_coefficient_explicit_power_decay : DecPow := by
  first | exact @GlobalTheory.SepReal.decPow | exact GlobalTheory.SepReal.decPow | (intros; apply GlobalTheory.SepReal.decPow <;> assumption)
