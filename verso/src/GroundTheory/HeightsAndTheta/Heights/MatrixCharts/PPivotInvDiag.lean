import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PivotInvDiag

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. By extensionality, compare the relevant components. Both sides reduce to the same expression.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem leadMinor_last_eq (hLL : LeadMinorLeading.Statement) (hLB : LeadMinorBasic.Statement)
    (d : ℕ) (S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    leadMinor S d = (S.submatrix Fin.castSucc Fin.castSucc).det := by
  have h := hLL (d + 1) S d (Nat.le_succ d) d le_rfl
  have hc : (Fin.castLE (Nat.le_succ d) : Fin d → Fin (d + 1)) = Fin.castSucc := by
    funext i; ext; rfl
  rw [hc] at h
  rw [← h]
  exact (hLB d (S.submatrix Fin.castSucc Fin.castSucc)).2.1

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions. Rewrite the conclusion using the stated equalities.
-/
theorem adjugate_last_last {d : ℕ} (S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    S.adjugate (Fin.last d) (Fin.last d) = (S.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  have : ((-1 : ℝ)) ^ ((Fin.last d : ℕ) + (Fin.last d : ℕ)) = 1 := by
    rw [← two_mul, pow_mul]; norm_num
  rw [this, one_mul]

end PivotInvDiag

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.
-/
theorem PivotInvDiag.proof (hLL : LeadMinorLeading.Statement) (hLB : LeadMinorBasic.Statement) :
    PivotInvDiag.Statement := by
  intro d S hS
  obtain ⟨-, hdet, hpos⟩ := hLB (d + 1) S
  have hm : 0 < leadMinor S d := hpos hS d (Nat.le_succ d)
  have hD : 0 < leadMinor S (d + 1) := hpos hS (d + 1) le_rfl
  rw [hdet] at hD
  have hmin := PivotInvDiag.leadMinor_last_eq hLL hLB d S
  unfold pivot
  rw [hdet, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply,
    PivotInvDiag.adjugate_last_last, ← hmin, smul_eq_mul]
  field_simp
