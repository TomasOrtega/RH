import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.IwaPf

open PositivityTheory.Rg.Sw

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Simplify using `[JJ, fromBlocks_multiply, Matrix.one_apply]`.
-/
theorem JJ_mul_self : JJ n * JJ n = -1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [JJ, fromBlocks_multiply, Matrix.one_apply]

/- English proof (translation)
Establish `h'` using `h`. Unfold `InG at h'`. Rewrite `h'` using `[← fromBlocks_toBlocks g, fromBlocks_conjTranspose, JJ, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add] at h'`. Take `⟨h1, h2, h3, h4⟩` from `h'`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← h1]`. Normalize the expressions using the abelian group laws. Rewrite using `[← h2]`. Normalize the expressions using the abelian group laws.

Rewrite using `[← h4]`. Normalize the expressions using the abelian group laws.
-/
theorem inG_blocks (g : M2 n) (h : InG g) :
    g.toBlocks₁₁ᴴ * g.toBlocks₂₁ - g.toBlocks₂₁ᴴ * g.toBlocks₁₁ = 0 ∧
    g.toBlocks₁₁ᴴ * g.toBlocks₂₂ - g.toBlocks₂₁ᴴ * g.toBlocks₁₂ = 1 ∧
    g.toBlocks₁₂ᴴ * g.toBlocks₂₂ - g.toBlocks₂₂ᴴ * g.toBlocks₁₂ = 0 := by
  have h' := h
  unfold InG at h'
  rw [← fromBlocks_toBlocks g, fromBlocks_conjTranspose, JJ, fromBlocks_multiply,
    fromBlocks_multiply, fromBlocks_inj] at h'
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, add_zero, zero_add] at h'
  obtain ⟨h1, h2, h3, h4⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · rw [← h1]; abel
  · rw [← h2]; abel
  · rw [← h4]; abel

/- English proof (translation)
Establish `hJ : JJ n * JJ n = -1` using `JJ_mul_self`. Establish `h1 : (-(JJ n * gᴴ * JJ n)) * g = 1`. Establish `e : gᴴ * JJ n * g = JJ n` using `h`. Rewrite using `[Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, e, hJ, neg_neg]`. Establish `h2` using `mul_eq_one_comm.mp h1`.

Establish `h3 : g * (JJ n * gᴴ * JJ n) = -1`. Rewrite `h2` using `[Matrix.mul_neg]`. Conclude with `neg_eq_iff_eq_neg.mp h2`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, hJ, Matrix.mul_neg, Matrix.mul_one, neg_neg]`.

Use `_ = JJ n := by rw [h3, Matrix.neg_mul, Matrix.one_mul, neg_neg]`.
-/
theorem inG_rows (g : M2 n) (h : InG g) : g * JJ n * gᴴ = JJ n := by
  have hJ : JJ n * JJ n = -1 := JJ_mul_self
  have h1 : (-(JJ n * gᴴ * JJ n)) * g = 1 := by
    have e : gᴴ * JJ n * g = JJ n := h
    rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, e, hJ, neg_neg]
  have h2 := mul_eq_one_comm.mp h1
  have h3 : g * (JJ n * gᴴ * JJ n) = -1 := by
    rw [Matrix.mul_neg] at h2
    exact neg_eq_iff_eq_neg.mp h2
  calc g * JJ n * gᴴ = -(g * (JJ n * gᴴ * JJ n) * JJ n) := by
        simp only [Matrix.mul_assoc, hJ, Matrix.mul_neg, Matrix.mul_one, neg_neg]
    _ = JJ n := by rw [h3, Matrix.neg_mul, Matrix.one_mul, neg_neg]

/- English proof (translation)
Establish `E2' : dᴴ * a - bᴴ * c = 1`. Establish `e` using `congrArg conjTranspose E2`. Simplify `e` using `[conjTranspose_sub, conjTranspose_mul]`. Establish `expand : (s • a + b)ᴴ * (s • c + d) - (s • c + d)ᴴ * (s • a + b) = (star s * s) • (aᴴ * c - cᴴ * a) + star s • (aᴴ * d - cᴴ * b) - s • (dᴴ * a - bᴴ * c) + (bᴴ * d - dᴴ * b)`. Simplify using `only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]`.

Use `module`. Rewrite using `[expand, E1, E2, E2', E3]`. Use `module`.
-/
theorem key (a b c d : Matrix (Fin n) (Fin n) ℂ) (E1 : aᴴ * c - cᴴ * a = 0) (E2 : aᴴ * d - cᴴ * b = 1)
    (E3 : bᴴ * d - dᴴ * b = 0) (s : ℂ) :
    (s • a + b)ᴴ * (s • c + d) - (s • c + d)ᴴ * (s • a + b) = (star s - s) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have E2' : dᴴ * a - bᴴ * c = 1 := by
    have e := congrArg conjTranspose E2
    simpa [conjTranspose_sub, conjTranspose_mul] using e
  have expand : (s • a + b)ᴴ * (s • c + d) - (s • c + d)ᴴ * (s • a + b)
      = (star s * s) • (aᴴ * c - cᴴ * a) + star s • (aᴴ * d - cᴴ * b)
        - s • (dᴴ * a - bᴴ * c) + (bᴴ * d - dᴴ * b) := by
    simp only [conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul]
    module
  rw [expand, E1, E2, E2', E3]
  module

/- English proof (translation)
Take `⟨E1, E2, E3⟩` from `inG_blocks g h`. Introduce `hdet`. Take `⟨v, hv, hYv⟩` from `exists_mulVec_eq_zero_iff.mpr hdet`. Establish `K` using `key g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₂₁ g.toBlocks₂₂ E1 E2 E3 s`. Use `set X := s • g.toBlocks₁₁ + g.toBlocks₁₂`.

Use `set Y := s • g.toBlocks₂₁ + g.toBlocks₂₂`. Establish `L : star v ⬝ᵥ ((Xᴴ * Y - Yᴴ * X) *ᵥ v) = 0`. Rewrite using `[Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hYv, Matrix.mulVec_zero, zero_sub, dotProduct_neg, dotProduct_mulVec, ← star_mulVec, hYv, star_zero, zero_dotProduct, neg_zero]`. Rewrite `L` using `[K, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]`. Break down `mul_eq_zero.mp L with h0 | h0` into its components or cases.

Conclude with `hs h0`. Conclude with `hv (dotProduct_star_self_eq_zero.mp h0)`.
-/
theorem det_ne (g : M2 n) (h : InG g) (s : ℂ) (hs : star s - s ≠ 0) : (s • g.toBlocks₂₁ + g.toBlocks₂₂).det ≠ 0 := by
  obtain ⟨E1, E2, E3⟩ := inG_blocks g h
  intro hdet
  obtain ⟨v, hv, hYv⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  have K := key g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₂₁ g.toBlocks₂₂ E1 E2 E3 s
  set X := s • g.toBlocks₁₁ + g.toBlocks₁₂
  set Y := s • g.toBlocks₂₁ + g.toBlocks₂₂
  have L : star v ⬝ᵥ ((Xᴴ * Y - Yᴴ * X) *ᵥ v) = 0 := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hYv,
      Matrix.mulVec_zero, zero_sub, dotProduct_neg, dotProduct_mulVec, ← star_mulVec,
      hYv, star_zero, zero_dotProduct, neg_zero]
  rw [K, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at L
  rcases mul_eq_zero.mp L with h0 | h0
  · exact hs h0
  · exact hv (dotProduct_star_self_eq_zero.mp h0)

end PositivityTheory.Rg.Sw.AbsSt.IwaPf
