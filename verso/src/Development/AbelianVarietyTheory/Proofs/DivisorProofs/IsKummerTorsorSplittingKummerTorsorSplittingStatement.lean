import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplitting
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsKummerTorsorSplittingKummerTorsorSplitting.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting : ∀ (q : ℕ) [NeZero q], IsKum q (kumT q) := by
  first
  | exact @GlobalTheory.EtC.KummerSplit.isKum_kumT
  | exact GlobalTheory.EtC.KummerSplit.isKum_kumT
  | (intros; apply GlobalTheory.EtC.KummerSplit.isKum_kumT <;> assumption)
