import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformLowerBoundOfSums
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CovTop.FromComp.uLow_of | exact GlobalTheory.CovTop.FromComp.uLow_of | (intros; apply GlobalTheory.CovTop.FromComp.uLow_of <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.uniform_lower_bound_of_sums : DeepGood → Size → Deg → Share → Height → HS → SumC → ULow := by
  first | exact @GlobalTheory.CovTop.FromComp.uLow_of | exact GlobalTheory.CovTop.FromComp.uLow_of | (intros; apply GlobalTheory.CovTop.FromComp.uLow_of <;> assumption)
