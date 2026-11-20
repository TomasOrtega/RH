import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

/- English proof (translation)
Introduce `x y`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (hM x k) (hN k y)`.
-/
private theorem matrix_mul_entries_mem_bot_subalgebra {A ι : Type} [Ring A] [Algebra ℂ A] [Fintype ι] {M N : Matrix ι ι A}
    (hM : ∀ x y, M x y ∈ (⊥ : Subalgebra ℂ A)) (hN : ∀ x y, N x y ∈ (⊥ : Subalgebra ℂ A)) :
    ∀ x y, (M * N) x y ∈ (⊥ : Subalgebra ℂ A) := by
  intro x y
  rw [Matrix.mul_apply]
  exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (hM x k) (hN k y)

/- English proof (translation)
Use `split_ifs`. Conclude with `hu`. Conclude with `Subalgebra.zero_mem _`.
-/
private theorem ite_zero_mem_bot_subalgebra {A : Type} [Ring A] [Algebra ℂ A] (p : Prop) [Decidable p] (u : A)
    (hu : u ∈ (⊥ : Subalgebra ℂ A)) : (if p then u else 0) ∈ (⊥ : Subalgebra ℂ A) := by
  split_ifs
  · exact hu
  · exact Subalgebra.zero_mem _

/- English proof (translation)
Introduce `A _ _ _ S _ _ s w`. Proceed by induction on `w with`. Consider the case `nil`. Introduce `a b`. Use `show (1 : Wd.SlopeTestRemainingChoices S A) a b ∈ _`.

Rewrite using `[Matrix.one_apply]`. Conclude with `ite_zero_mem_bot_subalgebra _ _ (Subalgebra.one_mem _)`. Consider the case `cons l w ih`. Introduce `a b`. Use `show ((Wd.ins l.intersection_update_fsHerm_neg_one (Wd.lift0 (YangianSpanCharacter.T.Uinv (if l.plus = true then s else star s))) : Wd.SlopeTestRemainingChoices S A) * (Wd.UUiw s w : Wd.SlopeTestRemainingChoices S A)) a b ∈ _`.

Use `matrix_mul_entries_mem_bot_subalgebra ?_ ih a b` and prove the remaining obligations. Introduce `x y`. Simplify using `only [Wd.ins, Matrix.sum_apply]`. Use `Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Use `matrix_mul_entries_mem_bot_subalgebra ?_ ?_ x y` and prove the remaining obligations.

Introduce `u v`. Simplify using `only [Wd.eU, Matrix.of_apply]`. Conclude with `ite_zero_mem_bot_subalgebra _ _ (Subalgebra.one_mem _)`. Introduce `u v`. Apply the tactic sequence `have hU : YangianSpanCharacter.T.Uinv (A := A) (if l.plus = true then s else star s) i j ∈ (⊥ : Subalgebra ℂ A) := by fin_cases i <;> fin_cases j <;>`.

Simplify using `[YangianSpanCharacter.T.Uinv, Subalgebra.one_mem, Subalgebra.zero_mem, Subalgebra.algebraMap_mem]`. Simplify using `only [Wd.lift0, Matrix.map_apply, Wd.io, Matrix.scalar_apply, Matrix.diagonal_apply]`. Conclude with `ite_zero_mem_bot_subalgebra _ _ hU`.
-/
theorem unipotent_scalar_identity : CutSH.UUiwScalar := by
  intro A _ _ _ S _ _ s w
  induction w with
  | nil =>
    intro a b
    show (1 : Wd.SlopeTestRemainingChoices S A) a b ∈ _
    rw [Matrix.one_apply]
    exact ite_zero_mem_bot_subalgebra _ _ (Subalgebra.one_mem _)
  | cons l w ih =>
    intro a b
    show ((Wd.ins l.intersection_update_fsHerm_neg_one (Wd.lift0 (YangianSpanCharacter.T.Uinv (if l.plus = true then s else star s))) : Wd.SlopeTestRemainingChoices S A) *
      (Wd.UUiw s w : Wd.SlopeTestRemainingChoices S A)) a b ∈ _
    refine matrix_mul_entries_mem_bot_subalgebra ?_ ih a b
    intro x y
    simp only [Wd.ins, Matrix.sum_apply]
    refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => ?_
    refine matrix_mul_entries_mem_bot_subalgebra ?_ ?_ x y
    · intro u v
      simp only [Wd.eU, Matrix.of_apply]
      exact ite_zero_mem_bot_subalgebra _ _ (Subalgebra.one_mem _)
    · intro u v
      have hU : YangianSpanCharacter.T.Uinv (A := A) (if l.plus = true then s else star s) i j ∈ (⊥ : Subalgebra ℂ A) := by
        fin_cases i <;> fin_cases j <;>
          simp [YangianSpanCharacter.T.Uinv, Subalgebra.one_mem, Subalgebra.zero_mem, Subalgebra.algebraMap_mem]
      simp only [Wd.lift0, Matrix.map_apply, Wd.io, Matrix.scalar_apply, Matrix.diagonal_apply]
      exact ite_zero_mem_bot_subalgebra _ _ hU

end Formalism.FourierDecayAlt.P
