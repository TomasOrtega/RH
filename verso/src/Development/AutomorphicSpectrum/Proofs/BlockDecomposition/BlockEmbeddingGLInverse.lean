import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL

variable (K : Type) [Field K]

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
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
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem blkEmb_row_ge {d j : ℕ} (A : Matrix (Fin j) (Fin j) K) (i l : Fin d)
    (hi : j ≤ (i : ℕ)) : blkEmb K d j A i l = if i = l then 1 else 0 := by
  simp only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]
  rw [dif_neg fun h => (not_lt.2 hi) h.1]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem blkEmb_col_ge {d j : ℕ} (A : Matrix (Fin j) (Fin j) K) (i l : Fin d)
    (hl : j ≤ (l : ℕ)) : blkEmb K d j A i l = if i = l then 1 else 0 := by
  simp only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]
  rw [dif_neg fun h => (not_lt.2 hl) h.2]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem blkEmb_lt {d j : ℕ} (A : Matrix (Fin j) (Fin j) K) (i l : Fin d)
    (hi : (i : ℕ) < j) (hl : (l : ℕ) < j) :
    blkEmb K d j A i l = A ⟨i, hi⟩ ⟨l, hl⟩ := by
  simp only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]
  rw [dif_pos ⟨hi, hl⟩]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
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
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
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
