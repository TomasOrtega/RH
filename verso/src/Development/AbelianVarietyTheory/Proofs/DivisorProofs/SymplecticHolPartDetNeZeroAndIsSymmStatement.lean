import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticHolPartDetNeZeroAndIsSymm
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSymplecticHolPartDetNeZeroAndIsSymm.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.symplectic_holPart_det_ne_zero_and_isSymm : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → P.det ≠ 0 ∧ (-(Q * P⁻¹)).IsSymm := by
  first | exact @GlobalTheory.SympBlocks.det_ne_zero_and_isSymm | exact GlobalTheory.SympBlocks.det_ne_zero_and_isSymm | (intros; apply GlobalTheory.SympBlocks.det_ne_zero_and_isSymm <;> assumption)
