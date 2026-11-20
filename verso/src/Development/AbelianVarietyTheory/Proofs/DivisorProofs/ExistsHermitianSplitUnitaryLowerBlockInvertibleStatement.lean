import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianSplitUnitaryLowerBlockInvertible
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsHermitianSplitUnitaryLowerBlockInvertible.lean&line=163#L163)
-/
theorem _root_.GlobalTheory.T.exists_hermitian_splitUnitary_lowerBlock_invertible : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (g : UG c (stdJ ν E)), ∃ t : Matrix ν ν E, (t.map c)ᵀ = t ∧ ((mat c g).toBlocks₂₁ + (mat c g).toBlocks₂₂ * t).det ≠ 0 := by
  first | exact @GlobalTheory.KSp.exists_herm_transverse | exact GlobalTheory.KSp.exists_herm_transverse | (intros; apply GlobalTheory.KSp.exists_herm_transverse <;> assumption)
