import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.FactsW
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.IdempotentCalculationHolds
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.GlueSmulSame

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem det_add_diagonal_cons {A : Type*} [CommRing A] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (a : A) (d : Fin n → A) :
    (M + diagonal (Fin.cons a d : Fin (n + 1) → A)).det =
      (M.submatrix Fin.succ Fin.succ + diagonal d).det * a +
        (M + diagonal (Fin.cons 0 d : Fin (n + 1) → A)).det := by
  set N := M + diagonal (Fin.cons 0 d : Fin (n + 1) → A) with hN
  have h1 : M + diagonal (Fin.cons a d : Fin (n + 1) → A) =
      N.updateRow 0 (N 0 + a • Pi.single 0 1) := by
    ext i j
    refine Fin.cases ?_ ?_ i
    · by_cases hj : j = 0
      · subst hj; simp [N]
      · simp [N, hj, Ne.symm hj]
    · intro i
      simp [N, Matrix.diagonal_apply]
  have h2 : (N.updateRow 0 (Pi.single 0 1)).det = (M.submatrix Fin.succ Fin.succ + diagonal d).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have hz : ∀ k : Fin n, (N.updateRow 0 (Pi.single 0 1)) 0 k.succ = 0 := by
      intro k; simp [Fin.succ_ne_zero]
    simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    simp only [Matrix.updateRow_self, Pi.single_eq_same, Fin.val_zero, pow_zero, one_mul,
      Fin.succAbove_zero]
    congr 1
    ext i j
    simp [N, Matrix.diagonal_apply]
  rw [h1, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, h2]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem shiftDiag_of (hS : ShiftOne) : ShiftDiag := by
  intro F E _ _ _ _ _ _ hc v n
  induction n with
  | zero =>
    intro M
    refine ⟨Fin.elim0, fun i => i.elim0, 1, ?_⟩
    simp [Matrix.det_isEmpty]
  | succ n ih =>
    intro M
    obtain ⟨t', ht', w', hw'⟩ := ih (M.submatrix Fin.succ Fin.succ)
    obtain ⟨t0, ht0, w, hw⟩ := hS F E hc v _
      ((M + diagonal (Fin.cons 0 (fun i => iA F E (t' i)) : Fin (n + 1) → _)).det) ⟨w', hw'⟩
    refine ⟨Fin.cons t0 t', ?_, w, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa using ht0
      · intro i; simpa using ht' i
    · have hf : (fun i => iA F E ((Fin.cons t0 t' : Fin (n + 1) → E) i)) =
          (Fin.cons (iA F E t0) (fun i => iA F E (t' i)) : Fin (n + 1) → _) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp
        · intro i; simp
      rw [hf, det_add_diagonal_cons]
      exact hw

end Formalism.L2.GenusGluing.Gen
