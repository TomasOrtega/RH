import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.FactsW
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.IdempotentCalculationHolds
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.GlueSmulSame

noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

/- English proof (translation)
Use `set N := M + diagonal (Fin.cons 0 d : Fin (n + 1) → A) with hN`. Establish `h1 : M + diagonal (Fin.cons a d : Fin (n + 1) → A) = N.updateRow 0 (N 0 + a • Pi.single 0 1)`. Use extensionality with `i j`. Use `Fin.cases ?_ ?_ i` and prove the remaining obligations. Distinguish the cases in `hj : j = 0`.

Substitute `hj` using the available equality. Simplify using `[N]`. Simplify using `[N, hj, Ne.symm hj]`. Introduce `i`. Simplify using `[N, Matrix.diagonal_apply]`.

Establish `h2 : (N.updateRow 0 (Pi.single 0 1)).det = (M.submatrix Fin.succ Fin.succ + diagonal d).det`. Rewrite using `[Matrix.det_succ_row_zero, Fin.sum_univ_succ]`. Establish `hz : ∀ k : Fin n, (N.updateRow 0 (Pi.single 0 1)) 0 k.succ = 0`. Introduce `k`. Simplify using `[Fin.succ_ne_zero]`.

Simplify using `only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]`. Simplify using `only [Matrix.updateRow_self, Pi.single_eq_same, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[N, Matrix.diagonal_apply]`.

Rewrite using `[h1, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, h2]`. Expand and normalize the polynomial expressions, which then agree.
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
Introduce `F E _ _ _ _ _ _ hc v n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `M`. Use `⟨Fin.elim0, fun i => i.elim0, 1, ?_⟩` and prove the remaining obligations.

Simplify using `[Matrix.det_isEmpty]`. Consider the case `succ n ih`. Introduce `M`. Take `⟨t', ht', w', hw'⟩` from `ih (M.submatrix Fin.succ Fin.succ)`. Take `⟨t0, ht0, w, hw⟩` from `hS F E hc v _ ((M + diagonal (Fin.cons 0 (fun i => iA F E (t' i)) : Fin (n + 1) → _)).det) ⟨w', hw'⟩`.

Use `⟨Fin.cons t0 t', ?_, w, ?_⟩` and prove the remaining obligations. Introduce `i`. Use `Fin.cases ?_ ?_ i` and prove the remaining obligations. Simplify using `using ht0`. Introduce `i`.

Simplify using `using ht' i`. Establish `hf : (fun i => iA F E ((Fin.cons t0 t' : Fin (n + 1) → E) i)) = (Fin.cons (iA F E t0) (fun i => iA F E (t' i)) : Fin (n + 1) → _)`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ ?_ i` and prove the remaining obligations. Simplify using the standard rewrite rules.

Introduce `i`. Simplify using the standard rewrite rules. Rewrite using `[hf, det_add_diagonal_cons]`. Conclude with `hw`.
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
