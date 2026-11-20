import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricMatrixInvNearOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixMulEntryNormLeUltrametricStatement

namespace GlobalTheory

/- English proof (translation)
Introduce `i j`. Establish `hXY : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1)`. Simplify using `only [sub_mul, mul_sub, mul_one, one_mul]`. Normalize the expressions using the abelian group laws. Establish `hp` using `GlobalTheory.T.norm_mul_apply_le_of_ultrametric E n (X - 1) (Y - 1) t t h0 h0 hX hY i j`.

Establish `htt : t * t ≤ t` using `by nlinarith`. Rewrite using `[hXY, Matrix.add_apply, Matrix.add_apply]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hp.trans htt))` and prove the remaining obligations. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hX i j) (hY i j))`.
-/
theorem norm_mul_sub_one_le_of_norm_sub_one_le {E : Type} [NormedField E] [IsUltrametricDist E]
    {n : Type} [Fintype n] [DecidableEq n] (X Y : Matrix n n E) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hX : ∀ i j, ‖(X - 1) i j‖ ≤ t) (hY : ∀ i j, ‖(Y - 1) i j‖ ≤ t) :
    ∀ i j, ‖(X * Y - 1) i j‖ ≤ t := by
  intro i j
  have hXY : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by
    simp only [sub_mul, mul_sub, mul_one, one_mul]; abel
  have hp := GlobalTheory.T.norm_mul_apply_le_of_ultrametric E n (X - 1) (Y - 1) t t h0 h0 hX hY i j
  have htt : t * t ≤ t := by nlinarith
  rw [hXY, Matrix.add_apply, Matrix.add_apply]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hp.trans htt))
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hX i j) (hY i j))

/- English proof (translation)
Introduce `l _ n _ _`. Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `ht : ∀ k : ℕ, 0 ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) ∧ (l : ℝ) ^ (-((k : ℤ) + 2)) < 1`. Introduce `k`. Use `⟨zpow_nonneg (by linarith) _, zpow_lt_one_of_neg₀ hl (by omega)⟩` and prove the remaining obligations.

Use `⟨fun k => { carrier := {X | ∀ i j, ‖((X : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))} one_mem' := by` and prove the remaining obligations. Introduce `i j`. Simplify using `using (ht k).1`. Use the proof step `mul_mem' := by`. Introduce `X Y hX hY`.

Simplify using `only [Set.mem_setOf_eq, Units.val_mul] at *`. Conclude with `norm_mul_sub_one_le_of_norm_sub_one_le _ _ _ (ht k).1 (ht k).2.le hX hY`. Use the proof step `inv_mem' := by`. Introduce `X hX`. Simplify using `only [Set.mem_setOf_eq] at *`.

Conclude with `GlobalTheory.T.ultrametric_matrix_inv_near_one ℚ_[l] n (X : Matrix n n ℚ_[l]) ((X⁻¹ : GL n ℚ_[l]) : Matrix n n ℚ_[l]) _ (ht k).1 (ht k).2 (Units.inv_mul X) hX }, fun k X => Iff.rfl⟩`.
-/
theorem congruenceSubgroups_GL_padic : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n],
    ∃ Γ : ℕ → Subgroup (GL n ℚ_[l]), ∀ k X, X ∈ Γ k ↔
      ∀ i j, ‖((X : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
  intro l _ n _ _
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have ht : ∀ k : ℕ, 0 ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) ∧ (l : ℝ) ^ (-((k : ℤ) + 2)) < 1 := by
    intro k
    refine ⟨zpow_nonneg (by linarith) _, zpow_lt_one_of_neg₀ hl (by omega)⟩
  refine ⟨fun k => {
    carrier := {X | ∀ i j, ‖((X : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))}
    one_mem' := by
      intro i j
      simpa using (ht k).1
    mul_mem' := by
      intro X Y hX hY
      simp only [Set.mem_setOf_eq, Units.val_mul] at *
      exact norm_mul_sub_one_le_of_norm_sub_one_le _ _ _ (ht k).1 (ht k).2.le hX hY
    inv_mem' := by
      intro X hX
      simp only [Set.mem_setOf_eq] at *
      exact GlobalTheory.T.ultrametric_matrix_inv_near_one ℚ_[l] n (X : Matrix n n ℚ_[l]) ((X⁻¹ : GL n ℚ_[l]) : Matrix n n ℚ_[l]) _
        (ht k).1 (ht k).2 (Units.inv_mul X) hX }, fun k X => Iff.rfl⟩

end GlobalTheory
