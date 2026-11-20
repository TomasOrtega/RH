import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairNormNeZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NormBigNe.normBig_ne` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBottomPairNormNeZero.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.bottom_pair_norm_ne_zero : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.GBig fun {D} _ _ _ G _ _ _ _ =>
  ∀ (δ t0 : ℂ) (i j : Fin D.R.m) t (Q : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q),
    GlobalTheory.FunObj.SqNum.IsBottom G t i j (GlobalTheory.SqTop.modT G t) P P' → P.norm ≠ 0 := by
  first | exact @GlobalTheory.NormBigNe.normBig_ne | exact GlobalTheory.NormBigNe.normBig_ne | (intros; apply GlobalTheory.NormBigNe.normBig_ne <;> assumption)
