import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonReadableAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.Exp.SerBase.readCmpAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FComparisonReadableAtPlace.lean&line=103#L103)
-/
theorem _root_.GlobalTheory.T.lagrangian_set_additive_subgroup : ReadCmpAt := by
  first | exact @GlobalTheory.BigOn.Exp.SerBase.readCmpAt | exact GlobalTheory.BigOn.Exp.SerBase.readCmpAt | (intros; apply GlobalTheory.BigOn.Exp.SerBase.readCmpAt <;> assumption)
