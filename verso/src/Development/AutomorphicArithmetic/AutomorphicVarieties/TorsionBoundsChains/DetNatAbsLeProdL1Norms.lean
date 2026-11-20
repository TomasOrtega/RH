import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Introduce `ι _ _ M`. Establish `key : |M.det| ≤ ∏ i, ∑ k, |M i k|`. Rewrite using `[← Matrix.det_transpose, Matrix.det_apply]`. Set `e : Equiv.Perm ι ↪ (ι → ι)` to `⟨fun σ => ⇑σ, DFunLike.coe_injective⟩`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>`. Simplify using `[h, Finset.abs_prod, Matrix.transpose_apply]`. Use `_ = ∑ f ∈ (Finset.univ : Finset (Equiv.Perm ι)).map e, ∏ i, |M i (f i)| := by`. Rewrite using `[Finset.sum_map]`.

Both sides reduce to the same expression. Use `_ ≤ ∑ f : ι → ι, ∏ i, |M i (f i)| := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun f _ _ => Finset.prod_nonneg fun i _ => abs_nonneg _)`. Use `_ = ∏ i, ∑ k, |M i k| := (Fintype.prod_sum (fun i k => |M i k|)).symm`. Establish `h2 : ((M.det.natAbs : ℕ) : ℤ) ≤ ((∏ i, ∑ k, (M i k).natAbs : ℕ) : ℤ)`. Use `push_cast`.

Simplify `key` using `[Int.natCast_natAbs]`. Conclude with `h2` after adjusting the coercions.
-/
theorem UpperTheory.V.KH.det_natAbs_le_prod_l1_norms :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ),
      M.det.natAbs ≤ ∏ i, ∑ k, (M i k).natAbs := by
  intro ι _ _ M
  have key : |M.det| ≤ ∏ i, ∑ k, |M i k| := by
    rw [← Matrix.det_transpose, Matrix.det_apply]
    let e : Equiv.Perm ι ↪ (ι → ι) := ⟨fun σ => ⇑σ, DFunLike.coe_injective⟩
    calc |∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, M.transpose (σ i) i|
        ≤ ∑ σ : Equiv.Perm ι, |Equiv.Perm.sign σ • ∏ i, M.transpose (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ σ : Equiv.Perm ι, ∏ i, |M i (σ i)| := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
            simp [h, Finset.abs_prod, Matrix.transpose_apply]
      _ = ∑ f ∈ (Finset.univ : Finset (Equiv.Perm ι)).map e, ∏ i, |M i (f i)| := by
          rw [Finset.sum_map]
          rfl
      _ ≤ ∑ f : ι → ι, ∏ i, |M i (f i)| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun f _ _ => Finset.prod_nonneg fun i _ => abs_nonneg _)
      _ = ∏ i, ∑ k, |M i k| := (Fintype.prod_sum (fun i k => |M i k|)).symm
  have h2 : ((M.det.natAbs : ℕ) : ℤ) ≤ ((∏ i, ∑ k, (M i k).natAbs : ℕ) : ℤ) := by
    push_cast
    simpa [Int.natCast_natAbs] using key
  exact_mod_cast h2
