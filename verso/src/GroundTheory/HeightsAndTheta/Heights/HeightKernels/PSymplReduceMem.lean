import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplReduceMem

/- English proof (translation)
Unfold `symplOmega`. Simplify using `only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem omega_sub_smul {l : Type} [Fintype l] [DecidableEq l] (u v w : l ⊕ l → ℝ) (c d : ℝ) :
    symplOmega (u - c • w) (v - d • w) =
      symplOmega u v - d * symplOmega u w - c * symplOmega w v + c * d * symplOmega w w := by
  unfold symplOmega
  simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring

/- English proof (translation)
Establish `key` using `(h2 ℝ n).2 (x (Sum.inl 0)) (x (Sum.inr 0)) (y (Sum.inl 0)) (y (Sum.inr 0)) (symplTail x) (symplTail y)`. Rewrite `key` using `[(h2 ℝ n).1 x, (h2 ℝ n).1 y]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem omega_tail (h2 : SymplCons.Statement) {n : ℕ} (x y : Fin (n + 1) ⊕ Fin (n + 1) → ℝ) :
    symplOmega (symplTail x) (symplTail y) =
      symplOmega x y - (x (Sum.inr 0) * y (Sum.inl 0) - x (Sum.inl 0) * y (Sum.inr 0)) := by
  have key := (h2 ℝ n).2 (x (Sum.inl 0)) (x (Sum.inr 0)) (y (Sum.inl 0)) (y (Sum.inr 0))
    (symplTail x) (symplTail y)
  rw [(h2 ℝ n).1 x, (h2 ℝ n).1 y] at key
  linarith

/- English proof (translation)
Apply the tactic sequence `rcases a with i | i <;> rcases b with j | j <;> simp [J, one_apply, Fin.succ_inj]`.
-/
theorem J_succ {n : ℕ} (a b : Fin n ⊕ Fin n) :
    J (Fin (n + 1)) ℝ (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) =
      J (Fin n) ℝ a b := by
  rcases a with i | i <;> rcases b with j | j <;> simp [J, one_apply, Fin.succ_inj]

/- English proof (translation)
Apply the tactic sequence `rcases a with i | i <;> simp [J, one_apply, Fin.succ_ne_zero]`.
-/
theorem J_succ_e {n : ℕ} (a : Fin n ⊕ Fin n) :
    J (Fin (n + 1)) ℝ (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) = 0 := by
  rcases a with i | i <;> simp [J, one_apply, Fin.succ_ne_zero]

/- English proof (translation)
Apply the tactic sequence `rcases b with j | j <;> simp [J, one_apply, (Fin.succ_ne_zero j).symm]`.
-/
theorem J_e_succ {n : ℕ} (b : Fin n ⊕ Fin n) :
    J (Fin (n + 1)) ℝ (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) = 0 := by
  rcases b with j | j <;> simp [J, one_apply, (Fin.succ_ne_zero j).symm]

/- English proof (translation)
Use function extensionality and compare the values at `b`. Simplify using `only [symplReduce, symplTail, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem reduce_row {n : ℕ} (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (a : Fin n ⊕ Fin n) :
    symplReduce H a = symplTail (H (Sum.map Fin.succ Fin.succ a)) -
      (H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) / H (Sum.inl 0) (Sum.inl 0)) •
        symplTail (H (Sum.inl 0)) := by
  funext b
  simp only [symplReduce, symplTail, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PSymplReduceMem

open PSymplReduceMem in

/- English proof (translation)
Introduce `n H hH he`. Establish `hω` using `(h1 ℝ (Fin (n + 1)) H).1 hH`. Rewrite using `[h1 ℝ (Fin n) (symplReduce H)]`. Introduce `a b`. Rewrite using `[reduce_row, reduce_row, omega_sub_smul, omega_tail h2, omega_tail h2, omega_tail h2, omega_tail h2, hω, hω, hω, hω, J_succ, J_succ_e, J_e_succ]`.

Simplify using `only [J, fromBlocks_apply₁₁, Matrix.zero_apply]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem SymplReduceMem.proof (h1 : SymplOmegaMem.Statement) (h2 : SymplCons.Statement) :
    SymplReduceMem.Statement := by
  intro n H hH he
  have hω := (h1 ℝ (Fin (n + 1)) H).1 hH
  rw [h1 ℝ (Fin n) (symplReduce H)]
  intro a b
  rw [reduce_row, reduce_row, omega_sub_smul, omega_tail h2, omega_tail h2, omega_tail h2,
    omega_tail h2, hω, hω, hω, hω, J_succ, J_succ_e, J_e_succ]
  simp only [J, fromBlocks_apply₁₁, Matrix.zero_apply]
  field_simp
  ring

end GroundTheory.Heights₂.Heights
