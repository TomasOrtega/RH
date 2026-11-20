import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob.DecH

variable {n : ℕ}

/- English proof (translation)
Unfold `JJ`. Rewrite using `[fromBlocks_multiply]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, neg_zero]`. Rewrite using `[← fromBlocks_one, fromBlocks_neg]`. Simplify using the standard rewrite rules.
-/
theorem jj_mul_jj : JJ n * JJ n = -1 := by
  unfold JJ
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, add_zero, zero_add, neg_zero]
  rw [← fromBlocks_one, fromBlocks_neg]
  simp

/- English proof (translation)
Establish `h' : gᴴ * (JJ n * g) = JJ n`. Rewrite using `[← Matrix.mul_assoc]`. Conclude with `h`. Establish `hK : (-(JJ n * gᴴ * JJ n)) * g = 1`. Simplify using `only [Matrix.neg_mul, Matrix.mul_assoc, h', jj_mul_jj, neg_neg]`.

Establish `hK' : g * (-(JJ n * gᴴ * JJ n)) = 1` using `mul_eq_one_comm.mp hK`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[jj_mul_jj, neg_neg, Matrix.mul_one]`. Use `_ = (g * -(JJ n * gᴴ * JJ n)) * JJ n := by`. Simplify using `only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]`.

Use `_ = JJ n := by rw [hK', Matrix.one_mul]`.
-/
theorem inG_dual {g : M2 n} (h : InG g) : g * JJ n * gᴴ = JJ n := by
  have h' : gᴴ * (JJ n * g) = JJ n := by
    rw [← Matrix.mul_assoc]
    exact h
  have hK : (-(JJ n * gᴴ * JJ n)) * g = 1 := by
    simp only [Matrix.neg_mul, Matrix.mul_assoc, h', jj_mul_jj, neg_neg]
  have hK' : g * (-(JJ n * gᴴ * JJ n)) = 1 := mul_eq_one_comm.mp hK
  calc g * JJ n * gᴴ = g * JJ n * gᴴ * (-(JJ n * JJ n)) := by
        rw [jj_mul_jj, neg_neg, Matrix.mul_one]
    _ = (g * -(JJ n * gᴴ * JJ n)) * JJ n := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = JJ n := by rw [hK', Matrix.one_mul]

/- English proof (translation)
Unfold `InG JJ at h`. Rewrite `h` using `[fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]`. Take `⟨h1, h2, -, h4⟩` from `h`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add] at h1 h2 h4`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← sub_eq_zero, ← h1]`. Normalize the expressions using the abelian group laws. Rewrite using `[← h2]`. Normalize the expressions using the abelian group laws. Rewrite using `[← sub_eq_zero, ← h4]`.

Normalize the expressions using the abelian group laws.
-/
theorem inG_blocks {A B C D : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks A B C D)) :
    Aᴴ * C = Cᴴ * A ∧ Aᴴ * D - Cᴴ * B = 1 ∧ Bᴴ * D = Dᴴ * B := by
  unfold InG JJ at h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h
  obtain ⟨h1, h2, -, h4⟩ := h
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, add_zero, zero_add] at h1 h2 h4
  refine ⟨?_, ?_, ?_⟩
  · rw [← sub_eq_zero, ← h1]
    abel
  · rw [← h2]
    abel
  · rw [← sub_eq_zero, ← h4]
    abel

/- English proof (translation)
Establish `h' : InG (fromBlocks Aᴴ Cᴴ Bᴴ Dᴴ)`. Establish `hd` using `inG_dual h`. Unfold `InG`. Rewrite using `[← fromBlocks_conjTranspose, conjTranspose_conjTranspose]`. Conclude with `hd`.

Take `⟨h1, h2, h3⟩` from `inG_blocks h'`. Simplify using `only [conjTranspose_conjTranspose] at h1 h2 h3`. Use `⟨h1, h2, ?_, h3⟩` and prove the remaining obligations. Establish `h4` using `congrArg conjTranspose h2`. Simplify using `only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_one] at h4`.

Rewrite using `[← neg_sub, h4]`.
-/
theorem inG_blocks_dual {A B C D : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks A B C D)) :
    A * Bᴴ = B * Aᴴ ∧ A * Dᴴ - B * Cᴴ = 1 ∧ C * Bᴴ - D * Aᴴ = -1 ∧ C * Dᴴ = D * Cᴴ := by
  have h' : InG (fromBlocks Aᴴ Cᴴ Bᴴ Dᴴ) := by
    have hd := inG_dual h
    unfold InG
    rw [← fromBlocks_conjTranspose, conjTranspose_conjTranspose]
    exact hd
  obtain ⟨h1, h2, h3⟩ := inG_blocks h'
  simp only [conjTranspose_conjTranspose] at h1 h2 h3
  refine ⟨h1, h2, ?_, h3⟩
  have h4 := congrArg conjTranspose h2
  simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_one] at h4
  rw [← neg_sub, h4]

end PositivityTheory.Rg.Sw.Glob.DecH
