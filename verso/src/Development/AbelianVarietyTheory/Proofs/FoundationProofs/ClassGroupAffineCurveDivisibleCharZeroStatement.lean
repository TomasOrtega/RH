import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupAffineCurveDivisibleCharZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FClassGroupAffineCurveDivisibleCharZero.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.classGroup_affineCurve_divisible_charZero : GlobalTheory.NeedB.ClDiv := by
  first | exact @GlobalTheory.classGroup_ringOfIntegers_divisible | exact GlobalTheory.classGroup_ringOfIntegers_divisible | (intros; apply GlobalTheory.classGroup_ringOfIntegers_divisible <;> assumption)
