import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

/- English proof (translation)
Introduce `d S`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[leadMinor]`. Unfold `leadMinor`. Use `congr 1`.

Use extensionality with `a b`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[dif_pos ⟨a.2, b.2⟩]`. Introduce `hS i hi`. Establish `e : (Matrix.of fun a b : Fin i => if h : (a : ℕ) < d ∧ (b : ℕ) < d then S ⟨a, h.1⟩ ⟨b, h.2⟩ else 0) = S.submatrix (Fin.castLE hi) (Fin.castLE hi)`.

Use extensionality with `a b`. Simplify using `only [Matrix.of_apply, Matrix.submatrix_apply]`. Rewrite using `[dif_pos ⟨a.2.trans_le hi, b.2.trans_le hi⟩]`. Both sides reduce to the same expression. Unfold `leadMinor`.

Rewrite using `[e]`. Conclude with `(hS.submatrix (Fin.castLE_injective hi)).det_pos`.
-/
theorem LeadMinorBasic.proof : LeadMinorBasic.Statement := by
  intro d S
  refine ⟨?_, ?_, ?_⟩
  · simp [leadMinor]
  · unfold leadMinor
    congr 1
    ext a b
    simp only [Matrix.of_apply]
    rw [dif_pos ⟨a.2, b.2⟩]
  · intro hS i hi
    have e : (Matrix.of fun a b : Fin i =>
        if h : (a : ℕ) < d ∧ (b : ℕ) < d then S ⟨a, h.1⟩ ⟨b, h.2⟩ else 0) =
        S.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
      ext a b
      simp only [Matrix.of_apply, Matrix.submatrix_apply]
      rw [dif_pos ⟨a.2.trans_le hi, b.2.trans_le hi⟩]
      rfl
    unfold leadMinor
    rw [e]
    exact (hS.submatrix (Fin.castLE_injective hi)).det_pos

end

end GroundTheory.Heights₂.Heights
