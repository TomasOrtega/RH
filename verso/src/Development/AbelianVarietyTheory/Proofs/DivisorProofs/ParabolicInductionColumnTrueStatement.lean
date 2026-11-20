import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicInductionColumnTrue
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothColRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SmGL.RowOneCell Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FParabolicInductionColumnTrue.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.parabolic_induction_column_true : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ), Nonempty ((parInd (colPart u v true) (colRep χ₁ χ₂ u v true)).Equiv
      (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) (χ₂ * absPow k (1 / 2))))) := by
  first | exact @GlobalTheory.SmGL.RowOneCell.colTwo_parInd_equiv_prod₂ | exact GlobalTheory.SmGL.RowOneCell.colTwo_parInd_equiv_prod₂ | (intros; apply GlobalTheory.SmGL.RowOneCell.colTwo_parInd_equiv_prod₂ <;> assumption)
