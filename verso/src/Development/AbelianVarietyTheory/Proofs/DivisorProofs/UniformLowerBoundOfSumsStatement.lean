import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformLowerBoundOfSums
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUniformLowerBoundOfSums.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.uniform_lower_bound_of_sums : DeepGood → Size → Deg → Share → Height → HS → SumC → ULow := by
  first | exact @GlobalTheory.CovTop.FromComp.uLow_of | exact GlobalTheory.CovTop.FromComp.uLow_of | (intros; apply GlobalTheory.CovTop.FromComp.uLow_of <;> assumption)
