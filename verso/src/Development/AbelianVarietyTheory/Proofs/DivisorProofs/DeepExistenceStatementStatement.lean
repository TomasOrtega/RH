import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepExistenceStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovTop.DeepExist.deepEx` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDeepExistenceStatement.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.deep_existence_statement : Hypotheses2 → DeepEx := by
  first | exact @GlobalTheory.CovTop.DeepExist.deepEx | exact GlobalTheory.CovTop.DeepExist.deepEx | (intros; apply GlobalTheory.CovTop.DeepExist.deepEx <;> assumption)
