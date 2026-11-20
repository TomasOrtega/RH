import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OwnPrimeIsUnitAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.Exp.SerBase.ownUnit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FOwnPrimeIsUnitAtPlace.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.ownPrime_isUnit_at_place : OwnUnit := by
  first | exact @GlobalTheory.BigOn.Exp.SerBase.ownUnit | exact GlobalTheory.BigOn.Exp.SerBase.ownUnit | (intros; apply GlobalTheory.BigOn.Exp.SerBase.ownUnit <;> assumption)
