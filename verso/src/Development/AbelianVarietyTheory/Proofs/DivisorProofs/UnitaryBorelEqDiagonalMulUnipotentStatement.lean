import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBorelEqDiagonalMulUnipotent
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryBorelEqDiagonalMulUnipotent.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.unitaryBorel_eq_diagonal_mul_unipotent : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (β : GU σ n), IsBorelU β →
    ∃ t ν : GU σ n, β = t * ν ∧ IsUnipU ν ∧
      (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) ∧
      ∀ i, ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((β : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
  first | exact @GlobalTheory.UnitaryBorel.borel_eq_diag_mul_unip_sameDiag | exact GlobalTheory.UnitaryBorel.borel_eq_diag_mul_unip_sameDiag | (intros; apply GlobalTheory.UnitaryBorel.borel_eq_diag_mul_unip_sameDiag <;> assumption)
