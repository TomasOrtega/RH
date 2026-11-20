import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ElementaryDivisorsExistDiscretelyValued
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FElementaryDivisorsExistDiscretelyValued.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.elementaryDivisors_exist_discretelyValued : Smith := by
  first | exact @GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued | exact GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued | (intros; apply GlobalTheory.InertZeta.elementaryDivisors_exist_discretely_valued <;> assumption)
