import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussA

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

/- English proof (translation)
Establish `h` using `hg`. Unfold `InG JJ at h`. Rewrite `h` using `[← Matrix.fromBlocks_toBlocks g, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul, Matrix.one_mul, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂] at h`. Take `⟨h1, h2, h3, h4⟩` from `Matrix.fromBlocks_inj.1 h`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `h1` as an intermediate fact. Rewrite `this` using `[neg_add_eq_sub, sub_eq_zero]`. Conclude with `this`. Use `h4` as an intermediate fact.

Rewrite `this` using `[neg_add_eq_sub, sub_eq_zero]`. Conclude with `this`. Use `h2` as an intermediate fact. Rewrite `this` using `[neg_add_eq_sub]`. Conclude with `this`.
-/
theorem inG_rel {g : M2 n} (hg : InG g) :
    g.toBlocks₁₁ᴴ * g.toBlocks₂₁ = g.toBlocks₂₁ᴴ * g.toBlocks₁₁ ∧
    g.toBlocks₁₂ᴴ * g.toBlocks₂₂ = g.toBlocks₂₂ᴴ * g.toBlocks₁₂ ∧
    g.toBlocks₁₁ᴴ * g.toBlocks₂₂ - g.toBlocks₂₁ᴴ * g.toBlocks₁₂ = 1 := by
  have h := hg
  unfold InG JJ at h
  rw [← Matrix.fromBlocks_toBlocks g, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul,
    Matrix.one_mul, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂] at h
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 h
  refine ⟨?_, ?_, ?_⟩
  · have := h1; rw [neg_add_eq_sub, sub_eq_zero] at this; exact this
  · have := h4; rw [neg_add_eq_sub, sub_eq_zero] at this; exact this
  · have := h2; rw [neg_add_eq_sub] at this; exact this

/- English proof (translation)
Take `⟨hG, hU⟩` from `hg`. Establish `hinv : g * gᴴ = 1` using `mul_eq_one_comm.1 hU`. Establish `hc : JJ n * g = g * JJ n`. Combine the equalities or inequalities in the displayed calculation. Unfold `JJ at hc`.

Rewrite `hc` using `[← Matrix.fromBlocks_toBlocks g, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul, Matrix.one_mul, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂] at hc`. Take `⟨h1, h2, h3, h4⟩` from `Matrix.fromBlocks_inj.1 hc`. Conclude with `⟨h1, h2⟩`.
-/
theorem inK_blocks {g : M2 n} (hg : InK g) : g.toBlocks₂₁ = -g.toBlocks₁₂ ∧ g.toBlocks₂₂ = g.toBlocks₁₁ := by
  obtain ⟨hG, hU⟩ := hg
  have hinv : g * gᴴ = 1 := mul_eq_one_comm.1 hU
  have hc : JJ n * g = g * JJ n := by
    calc JJ n * g = (g * gᴴ) * JJ n * g := by rw [hinv, Matrix.one_mul]
      _ = g * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
      _ = g * JJ n := by rw [hG]
  unfold JJ at hc
  rw [← Matrix.fromBlocks_toBlocks g, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hc
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, Matrix.neg_mul,
    Matrix.one_mul, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂] at hc
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 hc
  exact ⟨h1, h2⟩

end PositivityTheory.Rg.Sw.Glob.GaussH
