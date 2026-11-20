import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InCellIffDetNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FInCellIffDetNeZero.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.inCell_iff_det_lower_left_block_ne_zero : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (g : UG c (stdJ ν E)), InCell c g ↔ ((mat c g).toBlocks₂₁).det ≠ 0 := by
  first | exact @GlobalTheory.KSp.inCell_iff_det_ne_zero | exact GlobalTheory.KSp.inCell_iff_det_ne_zero | (intros; apply GlobalTheory.KSp.inCell_iff_det_ne_zero <;> assumption)
