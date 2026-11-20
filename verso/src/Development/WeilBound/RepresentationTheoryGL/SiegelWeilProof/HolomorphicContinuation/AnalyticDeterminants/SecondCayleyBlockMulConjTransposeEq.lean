import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt

noncomputable section

set_option linter.unusedSimpArgs false

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.LVs

open PositivityTheory.Rg.Sw

variable {n : ℕ}

/- English proof (translation)
Simplify using `[JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]`.
-/
theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  simp [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

/- English proof (translation)
Establish `h` using `congrArg Matrix.det hg`. Rewrite `h` using `[det_mul, det_mul, det_conjTranspose]`. Establish `hJ : (JJ n).det ≠ 0`. Introduce `h0`. Use `congrArg Matrix.det (JJ_mul_JJ (n := n))` as an intermediate fact.

Rewrite `this` using `[det_mul, h0, zero_mul, det_neg, det_one]`. Simplify using `at this`. Use `isUnit_iff_ne_zero.2 fun h0 => hJ ?_` and prove the remaining obligations. Rewrite `h` using `[h0, mul_zero]`. Conclude with `h.symm`.
-/
theorem isUnit_det_of_inG' {g : M2 n} (hg : InG g) : IsUnit g.det := by
  have h := congrArg Matrix.det hg
  rw [det_mul, det_mul, det_conjTranspose] at h
  have hJ : (JJ n).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (JJ_mul_JJ (n := n))
    rw [det_mul, h0, zero_mul, det_neg, det_one] at this
    simp at this
  refine isUnit_iff_ne_zero.2 fun h0 => hJ ?_
  rw [h0, mul_zero] at h
  exact h.symm

/- English proof (translation)
Establish `h1 : (-(JJ n) * gᴴ * JJ n) * g = 1`. Establish `: -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g)` using `by simp only [Matrix.mul_assoc]`. Rewrite using `[this, hg, Matrix.neg_mul, JJ_mul_JJ, neg_neg]`. Establish `h2 : g * (-(JJ n) * gᴴ * JJ n) = 1` using `mul_eq_one_comm.1 h1`. Establish `h3 : g * (-(JJ n) * gᴴ * JJ n) * JJ n = JJ n` using `by rw [h2, Matrix.one_mul]`.

Establish `h4 : g * (-(JJ n) * gᴴ * JJ n) * JJ n = g * JJ n * gᴴ`. Simplify using `only [Matrix.mul_assoc, JJ_mul_JJ, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, neg_neg]`. Rewrite using `[← h4, h3]`.
-/
theorem mul_JJ_conjTranspose {g : M2 n} (hg : InG g) : g * JJ n * gᴴ = JJ n := by
  have h1 : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
    have : -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
    rw [this, hg, Matrix.neg_mul, JJ_mul_JJ, neg_neg]
  have h2 : g * (-(JJ n) * gᴴ * JJ n) = 1 := mul_eq_one_comm.1 h1
  have h3 : g * (-(JJ n) * gᴴ * JJ n) * JJ n = JJ n := by rw [h2, Matrix.one_mul]
  have h4 : g * (-(JJ n) * gᴴ * JJ n) * JJ n = g * JJ n * gᴴ := by
    simp only [Matrix.mul_assoc, JJ_mul_JJ, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, neg_neg]
  rw [← h4, h3]

/- English proof (translation)
Establish `h` using `congrArg Matrix.toBlocks₂₂ (mul_JJ_conjTranspose hg)`. Rewrite `h` using `[← fromBlocks_toBlocks g]`. Simplify using `only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h`. Simplify using `only [Matrix.mul_zero, zero_add, Matrix.mul_neg, Matrix.mul_one, add_zero] at h`. Establish `: -(g.toBlocks₂₂ * g.toBlocks₂₁ᴴ) + g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = 0`.

Rewrite using `[← h]`. Simplify using the standard rewrite rules. Rewrite `this` using `[neg_add_eq_zero]`. Conclude with `this.symm`.
-/
theorem lower_rel {g : M2 n} (hg : InG g) : g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = g.toBlocks₂₂ * g.toBlocks₂₁ᴴ := by
  have h := congrArg Matrix.toBlocks₂₂ (mul_JJ_conjTranspose hg)
  rw [← fromBlocks_toBlocks g] at h
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₂] at h
  simp only [Matrix.mul_zero, zero_add, Matrix.mul_neg, Matrix.mul_one, add_zero] at h
  have : -(g.toBlocks₂₂ * g.toBlocks₂₁ᴴ) + g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = 0 := by
    rw [← h]; simp
  rw [neg_add_eq_zero] at this
  exact this.symm

/- English proof (translation)
Establish `h` using `lower_rel hg`. Simplify using `only [u1, conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Rewrite using `[h]`. Apply the tactic sequence `match_scalars <;> simp [Complex.I_mul_I] <;> ring_nf <;> simp [Complex.I_sq]`.
-/
theorem first_cayley_block_mul_conjTranspose_eq {g : M2 n} (hg : InG g) :
    u1 g * (u1 g)ᴴ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
  have h := lower_rel hg
  simp only [u1, conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h]
  match_scalars <;> simp [Complex.I_mul_I] <;> ring_nf <;> simp [Complex.I_sq]

/- English proof (translation)
Establish `h` using `lower_rel hg`. Simplify using `only [u2, conjTranspose_add, conjTranspose_neg, conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Rewrite using `[h]`. Apply the tactic sequence `match_scalars <;> simp [Complex.I_mul_I] <;> ring_nf <;> simp [Complex.I_sq]`.
-/
theorem second_cayley_block_mul_conjTranspose_eq {g : M2 n} (hg : InG g) :
    u2 g * (u2 g)ᴴ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
  have h := lower_rel hg
  simp only [u2, conjTranspose_add, conjTranspose_neg, conjTranspose_smul, Complex.star_def, Complex.conj_I,
    Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h]
  match_scalars <;> simp [Complex.I_mul_I] <;> ring_nf <;> simp [Complex.I_sq]

/- English proof (translation)
Establish `h1 : (-(JJ n) * gᴴ * JJ n) * g = 1`. Establish `: -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g)` using `by simp only [Matrix.mul_assoc]`. Rewrite using `[this, hg, Matrix.neg_mul, JJ_mul_JJ, neg_neg]`. Conclude with `Matrix.inv_eq_left_inv h1`.
-/
theorem inv_eq_of_inG {g : M2 n} (hg : InG g) : g⁻¹ = -(JJ n) * gᴴ * JJ n := by
  have h1 : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
    have : -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
    rw [this, hg, Matrix.neg_mul, JJ_mul_JJ, neg_neg]
  exact Matrix.inv_eq_left_inv h1

/- English proof (translation)
Rewrite using `[ub1, inv_eq_of_inG hg, u1]`. Use `conv_lhs => rw [← fromBlocks_toBlocks g]`. Simplify using `only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I]`. Simplify using `only [Matrix.zero_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, neg_zero, neg_neg]`. Use `module`.
-/
theorem inverse_first_block_eq_of_group {g : M2 n} (hg : InG g) : ub1 g = (u1 g)ᴴ := by
  rw [ub1, inv_eq_of_inG hg, u1]
  conv_lhs => rw [← fromBlocks_toBlocks g]
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₁₁,
    toBlocks_fromBlocks₂₁, conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I]
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg,
    zero_add, add_zero, neg_zero, neg_neg]
  module

/- English proof (translation)
Establish `hu : IsUnit gᴴ`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, det_conjTranspose]`. Conclude with `(isUnit_det_of_inG' hg).star`. Establish `hP : (gᴴᴴ * gᴴ).PosDef` using `Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 hu)`. Rewrite `hP` using `[conjTranspose_conjTranspose]`.

Establish `h2` using `hP.submatrix (e := (Sum.inr : Fin n → Fin n ⊕ Fin n)) Sum.inr_injective`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use `conv_rhs => rw [← fromBlocks_toBlocks g]`. Use extensionality with `i j`. Simplify using `[fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.submatrix]`.
-/
theorem posDef_lower {g : M2 n} (hg : InG g) :
    (g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ).PosDef := by
  have hu : IsUnit gᴴ := by
    rw [Matrix.isUnit_iff_isUnit_det, det_conjTranspose]
    exact (isUnit_det_of_inG' hg).star
  have hP : (gᴴᴴ * gᴴ).PosDef := Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_iff_isUnit.2 hu)
  rw [conjTranspose_conjTranspose] at hP
  have h2 := hP.submatrix (e := (Sum.inr : Fin n → Fin n ⊕ Fin n)) Sum.inr_injective
  convert h2 using 1
  conv_rhs => rw [← fromBlocks_toBlocks g]
  ext i j
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.submatrix]

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg Matrix.det (first_cayley_block_mul_conjTranspose_eq hg)`. Rewrite `h1` using `[det_mul, h, zero_mul]`. Conclude with `(posDef_lower hg).det_pos.ne' h1.symm`.
-/
theorem det_first_cayley_block_ne_zero {g : M2 n} (hg : InG g) : (u1 g).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (first_cayley_block_mul_conjTranspose_eq hg)
  rw [det_mul, h, zero_mul] at h1
  exact (posDef_lower hg).det_pos.ne' h1.symm

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg Matrix.det (second_cayley_block_mul_conjTranspose_eq hg)`. Rewrite `h1` using `[det_mul, h, zero_mul]`. Conclude with `(posDef_lower hg).det_pos.ne' h1.symm`.
-/
theorem det_second_cayley_block_ne_zero {g : M2 n} (hg : InG g) : (u2 g).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (second_cayley_block_mul_conjTranspose_eq hg)
  rw [det_mul, h, zero_mul] at h1
  exact (posDef_lower hg).det_pos.ne' h1.symm

/- English proof (translation)
Use `conv_lhs => rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks x, hP]`. Simplify using `only [u1, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, Matrix.mul_add, Matrix.mul_smul]`.
-/
theorem automorphy_first_mul_parabolic {P : M2 n} (x : M2 n) (hP : P.toBlocks₂₁ = 0) : u1 (P * x) = P.toBlocks₂₂ * u1 x := by
  conv_lhs => rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks x, hP]
  simp only [u1, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
    Matrix.mul_add, Matrix.mul_smul]

/- English proof (translation)
Use `conv_lhs => rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks x, hP]`. Simplify using `only [u2, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]`.
-/
theorem automorphy_second_mul_parabolic {P : M2 n} (x : M2 n) (hP : P.toBlocks₂₁ = 0) : u2 (P * x) = P.toBlocks₂₂ * u2 x := by
  conv_lhs => rw [← fromBlocks_toBlocks P, ← fromBlocks_toBlocks x, hP]
  simp only [u2, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]

/- English proof (translation)
Use `conv_lhs => rw [← fromBlocks_toBlocks P, hP]`. Conclude with `det_fromBlocks_zero₂₁ _ _ _`.
-/
theorem det_par {P : M2 n} (hP : P.toBlocks₂₁ = 0) : P.det = P.toBlocks₁₁.det * P.toBlocks₂₂.det := by
  conv_lhs => rw [← fromBlocks_toBlocks P, hP]
  exact det_fromBlocks_zero₂₁ _ _ _

/- English proof (translation)
Establish `h` using `congrArg Matrix.toBlocks₁₂ hG`. Rewrite `h` using `[← fromBlocks_toBlocks P, hP]`. Simplify `h` using `[JJ, fromBlocks_conjTranspose, fromBlocks_multiply]`.
-/
theorem par_rel {P : M2 n} (hG : InG P) (hP : P.toBlocks₂₁ = 0) : P.toBlocks₁₁ᴴ * P.toBlocks₂₂ = 1 := by
  have h := congrArg Matrix.toBlocks₁₂ hG
  rw [← fromBlocks_toBlocks P, hP] at h
  simpa [JJ, fromBlocks_conjTranspose, fromBlocks_multiply] using h

/- English proof (translation)
Establish `hA : IsUnit P.toBlocks₁₁.det`. Rewrite `hPu` using `[det_par hP]`. Conclude with `isUnit_of_mul_isUnit_left hPu`. Establish `hD : IsUnit P.toBlocks₂₂.det`. Rewrite `hPu` using `[det_par hP]`.

Conclude with `isUnit_of_mul_isUnit_right hPu`. Establish `hinv : P⁻¹ = fromBlocks (P.toBlocks₁₁)⁻¹ (-((P.toBlocks₁₁)⁻¹ * P.toBlocks₁₂ * (P.toBlocks₂₂)⁻¹)) 0 (P.toBlocks₂₂)⁻¹` using `by conv_lhs => rw [← fromBlocks_toBlocks P, hP]`. Use `Matrix.inv_eq_right_inv ?_` and prove the remaining obligations. Rewrite using `[fromBlocks_multiply]`. Simplify using `only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add, Matrix.mul_neg, Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hD]`.

Rewrite using `[← fromBlocks_one]`. Apply the tactic sequence `congr 1 <;> simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hD]`. Rewrite using `[ub1, ub1, Matrix.mul_inv_rev, hinv]`. Use `conv_lhs => rw [← fromBlocks_toBlocks x⁻¹]`. Simplify using `only [fromBlocks_multiply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, Matrix.mul_zero, add_zero, Matrix.add_mul, Matrix.smul_mul]`.
-/
theorem inverse_first_block_mul_parabolic {P x : M2 n} (hP : P.toBlocks₂₁ = 0) (hPu : IsUnit P.det) :
    ub1 (P * x) = ub1 x * (P.toBlocks₁₁)⁻¹ := by
  have hA : IsUnit P.toBlocks₁₁.det := by
    rw [det_par hP] at hPu; exact isUnit_of_mul_isUnit_left hPu
  have hD : IsUnit P.toBlocks₂₂.det := by
    rw [det_par hP] at hPu; exact isUnit_of_mul_isUnit_right hPu
  have hinv : P⁻¹ = fromBlocks (P.toBlocks₁₁)⁻¹ (-((P.toBlocks₁₁)⁻¹ * P.toBlocks₁₂ * (P.toBlocks₂₂)⁻¹)) 0
      (P.toBlocks₂₂)⁻¹ := by
    conv_lhs => rw [← fromBlocks_toBlocks P, hP]
    refine Matrix.inv_eq_right_inv ?_
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add, Matrix.mul_neg,
      Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hD]
    rw [← fromBlocks_one]
    congr 1 <;> simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hD]
  rw [ub1, ub1, Matrix.mul_inv_rev, hinv]
  conv_lhs => rw [← fromBlocks_toBlocks x⁻¹]
  simp only [fromBlocks_multiply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, Matrix.mul_zero, add_zero,
    Matrix.add_mul, Matrix.smul_mul]

/- English proof (translation)
Use `conv_lhs => rw [← fromBlocks_toBlocks g]`. Simplify using `[fromBlocks_conjTranspose, fromBlocks_multiply]`.
-/
theorem lower_mul_conjTranspose (g : M2 n) :
    (g * gᴴ).toBlocks₂₂ = g.toBlocks₂₁ * g.toBlocks₂₁ᴴ + g.toBlocks₂₂ * g.toBlocks₂₂ᴴ := by
  conv_lhs => rw [← fromBlocks_toBlocks g]
  simp [fromBlocks_conjTranspose, fromBlocks_multiply]

/- English proof (translation)
Rewrite using `[first_cayley_block_mul_conjTranspose_eq hk.1, ← lower_mul_conjTranspose, mul_eq_one_comm.1 hk.2]`. Simplify using `[← fromBlocks_one]`.
-/
theorem first_cayley_block_unitary {k : M2 n} (hk : InG k ∧ kᴴ * k = 1) : u1 k * (u1 k)ᴴ = 1 := by
  rw [first_cayley_block_mul_conjTranspose_eq hk.1, ← lower_mul_conjTranspose, mul_eq_one_comm.1 hk.2]
  simp [← fromBlocks_one]

/- English proof (translation)
Rewrite using `[second_cayley_block_mul_conjTranspose_eq hk.1, ← lower_mul_conjTranspose, mul_eq_one_comm.1 hk.2]`. Simplify using `[← fromBlocks_one]`.
-/
theorem second_cayley_block_unitary {k : M2 n} (hk : InG k ∧ kᴴ * k = 1) : u2 k * (u2 k)ᴴ = 1 := by
  rw [second_cayley_block_mul_conjTranspose_eq hk.1, ← lower_mul_conjTranspose, mul_eq_one_comm.1 hk.2]
  simp [← fromBlocks_one]

end PositivityTheory.Rg.Sw.LVs
