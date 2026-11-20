import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeJacquetRepEquivRow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothColRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SmGL.RowOneCell Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SmGL.RowOneCell.rowJac_swap_equiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRelativeJacquetRepEquivRow.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.relative_jacquet_rep_equiv_row : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ), Nonempty (Representation.Equiv ((relJac (rowPart u v) ((extTensor (detRep (Fin u) χ₁)
      (detRep (Fin (v + 1)) χ₂)).comp (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)).comp
        (swapBlocks k fun i j => Fin (sz u v i j))) (piTensor (colRep χ₁ χ₂ u v))) := by
  first | exact @GlobalTheory.SmGL.RowOneCell.rowJac_swap_equiv | exact GlobalTheory.SmGL.RowOneCell.rowJac_swap_equiv | (intros; apply GlobalTheory.SmGL.RowOneCell.rowJac_swap_equiv <;> assumption)
