import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicInductionColumnFalse
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothColRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SmGL.RowOneCell Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FParabolicInductionColumnFalse.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.parabolic_induction_column_false : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₂ → ∀ (u v : ℕ), Nonempty ((parInd (colPart u v false) (colRep χ₁ χ₂ u v false)).Equiv
      (detRep (Fin 1) (χ₂ * absPow k (-(v : ℂ) / 2)))) := by
  first | exact @GlobalTheory.SmGL.RowOneCell.parInd_colPart_false_equiv | exact GlobalTheory.SmGL.RowOneCell.parInd_colPart_false_equiv | (intros; apply GlobalTheory.SmGL.RowOneCell.parInd_colPart_false_equiv <;> assumption)
