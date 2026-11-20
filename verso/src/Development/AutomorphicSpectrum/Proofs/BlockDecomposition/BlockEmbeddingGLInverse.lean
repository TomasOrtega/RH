import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL

variable (K : Type) [Field K]

/- English proof (translation)
Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le hjd`. Rewrite using `[Fin.sum_univ_add]`. Establish `h0 : ∑ k : Fin m, f (Fin.natAdd j k) = 0` using `Finset.sum_eq_zero fun k _ => hf _ (by simp)`. Rewrite using `[h0, add_zero]`. Both sides reduce to the same expression.
-/
theorem sum_fin_of_ge_zero {d j : ℕ} (hjd : j ≤ d) (f : Fin d → K)
    (hf : ∀ k : Fin d, j ≤ (k : ℕ) → f k = 0) :
    ∑ k, f k = ∑ k : Fin j, f (Fin.castLE hjd k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjd
  rw [Fin.sum_univ_add]
  have h0 : ∑ k : Fin m, f (Fin.natAdd j k) = 0 :=
    Finset.sum_eq_zero fun k _ => hf _ (by simp)
  rw [h0, add_zero]
  rfl

/- English proof (translation)
Simplify using `only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]`. Rewrite using `[dif_neg fun h => (not_lt.2 hi) h.1]`.
-/
theorem blkEmb_row_ge {d j : ℕ} (A : Matrix (Fin j) (Fin j) K) (i l : Fin d)
    (hi : j ≤ (i : ℕ)) : blkEmb K d j A i l = if i = l then 1 else 0 := by
  simp only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]
  rw [dif_neg fun h => (not_lt.2 hi) h.1]

/- English proof (translation)
Simplify using `only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]`. Rewrite using `[dif_neg fun h => (not_lt.2 hl) h.2]`.
-/
theorem blkEmb_col_ge {d j : ℕ} (A : Matrix (Fin j) (Fin j) K) (i l : Fin d)
    (hl : j ≤ (l : ℕ)) : blkEmb K d j A i l = if i = l then 1 else 0 := by
  simp only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]
  rw [dif_neg fun h => (not_lt.2 hl) h.2]

/- English proof (translation)
Simplify using `only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]`. Rewrite using `[dif_pos ⟨hi, hl⟩]`.
-/
theorem blkEmb_lt {d j : ℕ} (A : Matrix (Fin j) (Fin j) K) (i l : Fin d)
    (hi : (i : ℕ) < j) (hl : (l : ℕ) < j) :
    blkEmb K d j A i l = A ⟨i, hi⟩ ⟨l, hl⟩ := by
  simp only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]
  rw [dif_pos ⟨hi, hl⟩]

/- English proof (translation)
Use extensionality with `i l`. Rewrite using `[Matrix.one_apply]`. Distinguish the cases in `hi : (i : ℕ) < j`. Distinguish the cases in `hl : (l : ℕ) < j`. Rewrite using `[GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ i l hi hl, Matrix.one_apply]`.

Simplify using `[Fin.ext_iff]`. Conclude with `GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K _ i l (not_lt.1 hl)`. Conclude with `GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K _ i l (not_lt.1 hi)`.
-/
theorem blkEmb_one (d j : ℕ) : blkEmb K d j (1 : Matrix (Fin j) (Fin j) K) = 1 := by
  ext i l
  rw [Matrix.one_apply]
  by_cases hi : (i : ℕ) < j
  · by_cases hl : (l : ℕ) < j
    · rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ i l hi hl, Matrix.one_apply]
      simp [Fin.ext_iff]
    · exact GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K _ i l (not_lt.1 hl)
  · exact GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K _ i l (not_lt.1 hi)

/- English proof (translation)
Use extensionality with `i l`. Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `hi : (i : ℕ) < j`. Distinguish the cases in `hl : (l : ℕ) < j`. Rewrite using `[GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ i l hi hl, Matrix.mul_apply, GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.sum_fin_of_ge_zero K hjd]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hk : ((Fin.castLE hjd k : Fin d) : ℕ) < j` using `k.2`. Rewrite using `[GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ i _ hi hk, GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ _ l hk hl]`. Both sides reduce to the same expression. Introduce `k hk`.

Rewrite using `[GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K _ i k hk, if_neg (by rintro rfl; omega), zero_mul]`. Establish `hl' : j ≤ (l : ℕ)` using `not_lt.1 hl`. Rewrite using `[GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K _ i l hl']`. Simplify using `only [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K B _ l hl', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K A i l hl']`. Establish `hi' : j ≤ (i : ℕ)` using `not_lt.1 hi`.

Rewrite using `[GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K _ i l hi']`. Simplify using `only [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K A i _ hi', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K B i l hi']`.
-/
theorem blkEmb_mul {d j : ℕ} (hjd : j ≤ d) (A B : Matrix (Fin j) (Fin j) K) :
    blkEmb K d j (A * B) = blkEmb K d j A * blkEmb K d j B := by
  ext i l
  rw [Matrix.mul_apply]
  by_cases hi : (i : ℕ) < j
  · by_cases hl : (l : ℕ) < j
    · rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ i l hi hl, Matrix.mul_apply,
        GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.sum_fin_of_ge_zero K hjd]
      · refine Finset.sum_congr rfl fun k _ => ?_
        have hk : ((Fin.castLE hjd k : Fin d) : ℕ) < j := k.2
        rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ i _ hi hk,
          GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ _ l hk hl]
        rfl
      · intro k hk
        rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K _ i k hk, if_neg (by rintro rfl; omega),
          zero_mul]
    · have hl' : j ≤ (l : ℕ) := not_lt.1 hl
      rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K _ i l hl']
      simp only [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K B _ l hl', mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
        GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K A i l hl']
  · have hi' : j ≤ (i : ℕ) := not_lt.1 hi
    rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K _ i l hi']
    simp only [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K A i _ hi', ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K B i l hi']

/- English proof (translation)
Introduce `K _ _ _ d j hjd g`. Use `⟨⟨GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb K d j (g : Matrix (Fin j) (Fin j) K), GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K), ?_, ?_⟩, rfl, rfl⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_mul K hjd, ← Units.val_mul, mul_inv_cancel, Units.val_one, GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_one]`. Rewrite using `[← GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_mul K hjd, ← Units.val_mul, inv_mul_cancel, Units.val_one, GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_one]`.
-/
theorem exists_gl_blkEmb : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j ≤ d →
    ∀ g : GL (Fin j) K, ∃ h : GL (Fin d) K,
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) ∧
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) := by
  intro K _ _ _ d j hjd g
  refine ⟨⟨GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb K d j (g : Matrix (Fin j) (Fin j) K),
    GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K), ?_, ?_⟩, rfl, rfl⟩
  · rw [← GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_mul K hjd, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_one]
  · rw [← GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_mul K hjd, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_one]

end GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL
