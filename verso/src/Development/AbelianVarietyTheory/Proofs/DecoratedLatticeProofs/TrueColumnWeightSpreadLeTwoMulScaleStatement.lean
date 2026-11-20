import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnWeightSpreadLeTwoMulScale
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FTrueColumnWeightSpreadLeTwoMulScale.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.trueColumnWeight_spread_le_two_mul_scale : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (CY : ℝ), HtRowsS L CY → 8 ≤ L.sc.X' → 2 ≤ L.sc.x → ∀ (u : B.Word) (j : ℕ), j ≤ B.R.m → ∀ τ, ((B.wts.lamTrue u j τ).spread : ℝ) ≤ 2 * L.sc.a := by
  first | exact @GlobalTheory.CoreHt.SpreadBound.spread_lamTrue_le | exact GlobalTheory.CoreHt.SpreadBound.spread_lamTrue_le | (intros; apply GlobalTheory.CoreHt.SpreadBound.spread_lamTrue_le <;> assumption)
