import Mathlib
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply

open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.KDelFormula

variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `[Fin.removeNth]`. Simplify using `[Fin.removeNth, Fin.succ_succAbove_succ]`.
-/
theorem removeNth_succ_vecCons {n : ℕ} (x : P) (Y : Fin (n + 1) → P) (t : Fin (n + 1)) :
    t.succ.removeNth (Matrix.vecCons x Y) = Matrix.vecCons x (t.removeNth Y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Fin.removeNth]
  · simp [Fin.removeNth, Fin.succ_succAbove_succ]

/- English proof (translation)
Establish `hW : Matrix.vecCons x (t.removeNth Y) = Function.update Y t x ∘ t.cycleRange.symm`. Rewrite using `[← Fin.cons_removeNth_eq_comp_cycleRange_symm]`. Simplify using `only [Function.update_self, Fin.removeNth_update]`. Both sides reduce to the same expression. Rewrite using `[hW, η.map_perm, Equiv.Perm.sign_symm, Fin.sign_cycleRange, Units.smul_def]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem map_vecCons_removeNth {n : ℕ} (η : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (x : P)
    (Y : Fin (n + 1) → P) (t : Fin (n + 1)) :
    η (Matrix.vecCons x (t.removeNth Y)) = (-1 : ℤ) ^ (t : ℕ) • η (Function.update Y t x) := by
  have hW : Matrix.vecCons x (t.removeNth Y) = Function.update Y t x ∘ t.cycleRange.symm := by
    rw [← Fin.cons_removeNth_eq_comp_cycleRange_symm]
    simp only [Function.update_self, Fin.removeNth_update]
    rfl
  rw [hW, η.map_perm, Equiv.Perm.sign_symm, Fin.sign_cycleRange, Units.smul_def]
  push_cast
  rfl

/- English proof (translation)
Establish `hs : ∀ t : ℕ, ((-1 : ℤ) ^ (t + 1) * (-1) ^ t) = -1` using `fun t => by`. Rewrite using `[← pow_add]`. Conclude with `Odd.neg_one_pow ⟨t, by ring⟩`. Consider the cases of `q with`. Consider the case `zero`.

Rewrite using `[kD_apply, Fin.sum_univ_succ]`. Simplify using `[Fin.removeNth_zero]`. Consider the case `succ n`. Rewrite using `[kD_apply, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`.

Simplify using `[Fin.removeNth_zero]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.val_succ, Matrix.cons_val_succ, removeNth_succ_vecCons, map_vecCons_removeNth, map_zsmul, smul_smul, hs, neg_one_zsmul]`.
-/
theorem kD_vecCons (T : P →ₗ[ℝ] Module.End ℂ M) {q : ℕ} (η : P [⋀^Fin q]→ₗ[ℝ] M) (x : P)
    (Y : Fin q → P) :
    kD T η (Matrix.vecCons x Y) =
      T x (η Y) - ∑ t, T (Y t) (η (Function.update Y t x)) := by
  have hs : ∀ t : ℕ, ((-1 : ℤ) ^ (t + 1) * (-1) ^ t) = -1 := fun t => by
    rw [← pow_add]
    exact Odd.neg_one_pow ⟨t, by ring⟩
  cases q with
  | zero =>
    rw [kD_apply, Fin.sum_univ_succ]
    simp [Fin.removeNth_zero]
  | succ n =>
    rw [kD_apply, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · simp [Fin.removeNth_zero]
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [Fin.val_succ, Matrix.cons_val_succ, removeNth_succ_vecCons, map_vecCons_removeNth,
        map_zsmul, smul_smul, hs, neg_one_zsmul]

/- English proof (translation)
Rewrite using `[kDel_apply]`. Simplify using `only [kD_vecCons, map_sub, map_sum, Finset.sum_sub_distrib]`. Use `congr 1`. Conclude with `Finset.sum_comm`.
-/
theorem kDel_kD {β : Type} [Fintype β] (T T' : P →ₗ[ℝ] Module.End ℂ M) (b : β → P) {q : ℕ}
    (η : P [⋀^Fin q]→ₗ[ℝ] M) (Y : Fin q → P) :
    kDel T' b (kD T η) Y = ∑ i, T' (b i) (T (b i) (η Y)) -
      ∑ t, ∑ i, T' (b i) (T (Y t) (η (Function.update Y t (b i)))) := by
  rw [kDel_apply]
  simp only [kD_vecCons, map_sub, map_sum, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

end GlobalTheory.CompanionTheory.KDelFormula
