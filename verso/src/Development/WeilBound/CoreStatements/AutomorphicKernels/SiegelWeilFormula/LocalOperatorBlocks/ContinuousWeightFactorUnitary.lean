import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.LongWeylFunctional

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

/- English proof (translation)
Introduce `x y h`. Conclude with `Subtype.ext (Units.ext h)`.
-/
theorem mR_injective : Function.Injective (mR : GR n → M2 n) := by
  intro x y h
  exact Subtype.ext (Units.ext h)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_mul (x y : GR n) : mR (x * y) = mR x * mR y := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_one : mR (1 : GR n) = 1 := rfl

/- English proof (translation)
Simplify using `[JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg, ← Matrix.fromBlocks_one]`.
-/
theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  simp [JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_neg, ← Matrix.fromBlocks_one]

/- English proof (translation)
Introduce `h0`. Establish `e` using `congrArg Matrix.det (JJ_mul_JJ (n := n))`. Rewrite `e` using `[Matrix.det_mul, h0, zero_mul, Matrix.det_neg, Matrix.det_one, mul_one]`. Conclude with `(pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) e.symm`.
-/
theorem JJ_det_ne : (JJ n).det ≠ 0 := by
  intro h0
  have e := congrArg Matrix.det (JJ_mul_JJ (n := n))
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_neg, Matrix.det_one, mul_one] at e
  exact (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) e.symm

/- English proof (translation)
Establish `e` using `congrArg Matrix.det h`. Rewrite `e` using `[Matrix.det_mul, Matrix.det_mul]`. Use `isUnit_iff_ne_zero.2 fun h0 => ?_` and prove the remaining obligations. Rewrite `e` using `[h0, mul_zero]`. Conclude with `JJ_det_ne e.symm`.
-/
theorem det_ne_of_inG {M : M2 n} (h : InG M) : IsUnit M.det := by
  have e := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at e
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, mul_zero] at e
  exact JJ_det_ne e.symm

def toGR (M : M2 n) (h : InG M) : GR n := ⟨Matrix.nonsingInvUnit M (det_ne_of_inG h), h⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_toGR (M : M2 n) (h : InG M) : mR (toGR M h) = M := rfl

/- English proof (translation)
Establish `h1 : IsUnit (aᴴ).det` using `by rw [Matrix.det_conjTranspose]; exact ha.star`. Simplify using `[InG, mLc, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_nonsing_inv, Matrix.mul_nonsing_inv _ h1, Matrix.nonsing_inv_mul _ ha]`.
-/
theorem inG_mLc {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) : InG (mLc a) := by
  have h1 : IsUnit (aᴴ).det := by rw [Matrix.det_conjTranspose]; exact ha.star
  simp [InG, mLc, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_nonsing_inv,
    Matrix.mul_nonsing_inv _ h1, Matrix.nonsing_inv_mul _ ha]

/- English proof (translation)
Simplify using `[InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]`.
-/
theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  simp [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]

/- English proof (translation)
Simplify using `[InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]`.
-/
theorem inG_JJ : InG (JJ n) := by
  simp [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

open scoped Classical in

def mG (a : Matrix (Fin n) (Fin n) ℂ) : GR n := if h : IsUnit a.det then toGR _ (inG_mLc h) else 1

/- English proof (translation)
Unfold `mG`. Rewrite using `[dif_pos ha]`. Both sides reduce to the same expression.
-/
theorem mR_mG {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) : mR (mG a) = mLc a := by
  unfold mG; rw [dif_pos ha]; rfl

open scoped Classical in

def nG (b : Matrix (Fin n) (Fin n) ℂ) : GR n := if h : bᴴ = b then toGR _ (inG_nU h) else 1

/- English proof (translation)
Unfold `nG`. Rewrite using `[dif_pos hb]`. Both sides reduce to the same expression.
-/
theorem mR_nG {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : mR (nG b) = nU b := by
  unfold nG; rw [dif_pos hb]; rfl

def jG (n : ℕ) : GR n := toGR _ inG_JJ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_jG : mR (jG n) = JJ n := rfl

/- English proof (translation)
Establish `e : (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂)ᴴ * JJ n * Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ = JJ n`. Rewrite using `[Matrix.fromBlocks_toBlocks]`. Conclude with `h`. Simplify using `only [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at e`. Take `⟨e1, e2, -, e4⟩` from `e`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `e1` as an intermediate fact. Simplify using `at this`. Conclude with `(neg_add_eq_zero.1 this).symm`. Use `e2` as an intermediate fact.

Simplify using `at this`. Rewrite using `[sub_eq_neg_add]`. Conclude with `this`. Use `e4` as an intermediate fact. Simplify using `at this`.

Conclude with `(neg_add_eq_zero.1 this).symm`.
-/
theorem inG_blocks {M : M2 n} (h : InG M) :
    M.toBlocks₁₁ᴴ * M.toBlocks₂₁ = M.toBlocks₂₁ᴴ * M.toBlocks₁₁ ∧
    M.toBlocks₁₁ᴴ * M.toBlocks₂₂ - M.toBlocks₂₁ᴴ * M.toBlocks₁₂ = 1 ∧
    M.toBlocks₁₂ᴴ * M.toBlocks₂₂ = M.toBlocks₂₂ᴴ * M.toBlocks₁₂ := by
  have e : (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂)ᴴ * JJ n *
      Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ = JJ n := by
    rw [Matrix.fromBlocks_toBlocks]; exact h
  simp only [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at e
  obtain ⟨e1, e2, -, e4⟩ := e
  refine ⟨?_, ?_, ?_⟩
  · have := e1; simp at this; exact (neg_add_eq_zero.1 this).symm
  · have := e2; simp at this; rw [sub_eq_neg_add]; exact this
  · have := e4; simp at this; exact (neg_add_eq_zero.1 this).symm

/- English proof (translation)
Take `⟨-, hAD, hBD⟩` from `inG_blocks (M := mR y) y.2`. Use `set A := (mR y).toBlocks₁₁`. Use `set B := (mR y).toBlocks₁₂`. Use `set D := (mR y).toBlocks₂₂`. Rewrite `hAD` using `[h, Matrix.conjTranspose_zero, Matrix.zero_mul, sub_zero]`.

Establish `hA : IsUnit A.det`. Establish `h1` using `congrArg Matrix.det hAD`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_one, Matrix.det_conjTranspose]`. Conclude with `isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at h1`. Establish `hD : D = (Aᴴ)⁻¹` using `(Matrix.inv_eq_right_inv hAD).symm`.

Establish `hb : (A⁻¹ * B)ᴴ = A⁻¹ * B`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, ← hD, hBD, hD, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose]`. Use `⟨A, A⁻¹ * B, hA, hb, mR_injective ?_⟩` and prove the remaining obligations. Rewrite using `[mR_mul, mR_mG hA, mR_nG hb, mLc, nU, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_toBlocks (mR y)]`. Simplify using `only [Matrix.mul_one, Matrix.zero_mul, add_zero, Matrix.mul_zero, zero_add, Matrix.mul_nonsing_inv_cancel_left _ _ hA]`.

Rewrite using `[h]`. Use `show Matrix.fromBlocks A B 0 D = Matrix.fromBlocks A B 0 (Aᴴ)⁻¹`. Rewrite using `[← hD]`.
-/
theorem par_eq (y : GR n) (h : (mR y).toBlocks₂₁ = 0) :
    ∃ a b : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ bᴴ = b ∧ y = mG a * nG b := by
  obtain ⟨-, hAD, hBD⟩ := inG_blocks (M := mR y) y.2
  set A := (mR y).toBlocks₁₁
  set B := (mR y).toBlocks₁₂
  set D := (mR y).toBlocks₂₂
  rw [h, Matrix.conjTranspose_zero, Matrix.zero_mul, sub_zero] at hAD
  have hA : IsUnit A.det := by
    have h1 := congrArg Matrix.det hAD
    rw [Matrix.det_mul, Matrix.det_one, Matrix.det_conjTranspose] at h1
    exact isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at h1
  have hD : D = (Aᴴ)⁻¹ := (Matrix.inv_eq_right_inv hAD).symm
  have hb : (A⁻¹ * B)ᴴ = A⁻¹ * B := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, ← hD, hBD, hD, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_conjTranspose]
  refine ⟨A, A⁻¹ * B, hA, hb, mR_injective ?_⟩
  rw [mR_mul, mR_mG hA, mR_nG hb, mLc, nU, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_toBlocks (mR y)]
  simp only [Matrix.mul_one, Matrix.zero_mul, add_zero, Matrix.mul_zero, zero_add, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  rw [h]
  show Matrix.fromBlocks A B 0 D = Matrix.fromBlocks A B 0 (Aᴴ)⁻¹
  rw [← hD]

/- English proof (translation)
The claim follows from `mR_injective (by rw [mR_mul, mR_jG, mR_nG hb, h])`.
-/
theorem eq_jn (g : GR n) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) (h : mR g = JJ n * nU b) : g = jG n * nG b :=
  mR_injective (by rw [mR_mul, mR_jG, mR_nG hb, h])

/- English proof (translation)
Use `conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]`. Rewrite using `[Matrix.fromBlocks_mulVec]`. Both sides reduce to the same expression.
-/
theorem mulVec_blocks (M : M2 n) (x y : Fin n → ℂ) :
    M *ᵥ Sum.elim x y = Sum.elim (M.toBlocks₁₁ *ᵥ x + M.toBlocks₁₂ *ᵥ y) (M.toBlocks₂₁ *ᵥ x + M.toBlocks₂₂ *ᵥ y) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  rw [Matrix.fromBlocks_mulVec]
  rfl

/- English proof (translation)
Rewrite using `[JJ, Matrix.fromBlocks_mulVec]`. Simplify using `[dotProduct, Fintype.sum_sum_type, Matrix.neg_mulVec, sub_eq_add_neg]`.
-/
theorem dot_JJ (x y : Fin n → ℂ) :
    star (Sum.elim x y) ⬝ᵥ (JJ n *ᵥ Sum.elim x y) = star x ⬝ᵥ y - star y ⬝ᵥ x := by
  rw [JJ, Matrix.fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type, Matrix.neg_mulVec, sub_eq_add_neg]

/- English proof (translation)
Use `conv_rhs => rw [← h]`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]`.
-/
theorem inG_dot {M : M2 n} (h : InG M) (z : Fin n ⊕ Fin n → ℂ) :
    star (M *ᵥ z) ⬝ᵥ (JJ n *ᵥ (M *ᵥ z)) = star z ⬝ᵥ (JJ n *ᵥ z) := by
  conv_rhs => rw [← h]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

open scoped ComplexOrder in
/- English proof (translation)
Take `⟨x, hx0, hx⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Establish `e` using `inG_dot (M := mR g) g.2 (Sum.elim (c • x) x)`. Rewrite `e` using `[mulVec_blocks]`. Establish `hlow : (mR g).toBlocks₂₁ *ᵥ (c • x) + (mR g).toBlocks₂₂ *ᵥ x = 0`. Rewrite using `[← hx, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul]`.

Rewrite `e` using `[hlow, dot_JJ, dot_JJ]`. Simplify using `only [star_zero, zero_dotProduct, dotProduct_zero, sub_zero, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at e`. Establish `hxx : star x ⬝ᵥ x ≠ 0` using `fun h => hx0 (dotProduct_star_self_eq_zero.1 h)`. Establish `: (star c - c) * (star x ⬝ᵥ x) = 0` using `by rw [sub_mul]; exact e.symm`. Break down `mul_eq_zero.1 this with h | h` into its components or cases.

Conclude with `hc h`. Conclude with `hxx h`.
-/
theorem automorphy_det_ne_zero_of_im (g : GR n) (c : ℂ) (hc : star c - c ≠ 0)
    (h0 : (c • (mR g).toBlocks₂₁ + (mR g).toBlocks₂₂).det = 0) : False := by
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have e := inG_dot (M := mR g) g.2 (Sum.elim (c • x) x)
  rw [mulVec_blocks] at e
  have hlow : (mR g).toBlocks₂₁ *ᵥ (c • x) + (mR g).toBlocks₂₂ *ᵥ x = 0 := by
    rw [← hx, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul]
  rw [hlow, dot_JJ, dot_JJ] at e
  simp only [star_zero, zero_dotProduct, dotProduct_zero, sub_zero, star_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul] at e
  have hxx : star x ⬝ᵥ x ≠ 0 := fun h => hx0 (dotProduct_star_self_eq_zero.1 h)
  have : (star c - c) * (star x ⬝ᵥ x) = 0 := by rw [sub_mul]; exact e.symm
  rcases mul_eq_zero.1 this with h | h
  · exact hc h
  · exact hxx h

/- English proof (translation)
Introduce `h0` and use `automorphy_det_ne_zero_of_im g Complex.I (by norm_num [Complex.ext_iff]) (by rw [u1] at h0; exact h0)`.
-/
theorem automorphy_first_det_ne_zero (g : GR n) : (u1 (mR g)).det ≠ 0 := fun h0 =>
  automorphy_det_ne_zero_of_im g Complex.I (by norm_num [Complex.ext_iff]) (by rw [u1] at h0; exact h0)

/- English proof (translation)
Introduce `h0` and use `automorphy_det_ne_zero_of_im g (-Complex.I) (by norm_num [Complex.ext_iff]) (by rw [u2, ← neg_smul] at h0; exact h0)`.
-/
theorem automorphy_second_det_ne_zero (g : GR n) : (u2 (mR g)).det ≠ 0 := fun h0 =>
  automorphy_det_ne_zero_of_im g (-Complex.I) (by norm_num [Complex.ext_iff]) (by rw [u2, ← neg_smul] at h0; exact h0)

/- English proof (translation)
Use `conv_lhs => rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks N, Matrix.fromBlocks_multiply]`. Both sides reduce to the same expression.
-/
theorem lower_left_block_mul (M N : M2 n) : (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks N, Matrix.fromBlocks_multiply]
  rfl

/- English proof (translation)
Use `conv_lhs => rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks N, Matrix.fromBlocks_multiply]`. Both sides reduce to the same expression.
-/
theorem lower_right_block_mul (M N : M2 n) : (M * N).toBlocks₂₂ = M.toBlocks₂₁ * N.toBlocks₁₂ + M.toBlocks₂₂ * N.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks N, Matrix.fromBlocks_multiply]
  rfl

/- English proof (translation)
Simplify using `[u1, lower_left_block_mul, lower_right_block_mul, h, Matrix.mul_add, Matrix.mul_smul]`.
-/
theorem automorphy_first_mul_parabolic (M N : M2 n) (h : M.toBlocks₂₁ = 0) : u1 (M * N) = M.toBlocks₂₂ * u1 N := by
  simp [u1, lower_left_block_mul, lower_right_block_mul, h, Matrix.mul_add, Matrix.mul_smul]

/- English proof (translation)
Simplify using `[u2, lower_left_block_mul, lower_right_block_mul, h, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]`.
-/
theorem automorphy_second_mul_parabolic (M N : M2 n) (h : M.toBlocks₂₁ = 0) : u2 (M * N) = M.toBlocks₂₂ * u2 N := by
  simp [u2, lower_left_block_mul, lower_right_block_mul, h, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]

/- English proof (translation)
Simplify using `[u1, h]`.
-/
theorem automorphy_first_parabolic (M : M2 n) (h : M.toBlocks₂₁ = 0) : u1 M = M.toBlocks₂₂ := by simp [u1, h]

/- English proof (translation)
Simplify using `[u2, h]`.
-/
theorem automorphy_second_parabolic (M : M2 n) (h : M.toBlocks₂₁ = 0) : u2 M = M.toBlocks₂₂ := by simp [u2, h]

/- English proof (translation)
Establish `h21 : (1 : M2 n).toBlocks₂₁ = 0` using `by rw [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₁]`. Establish `h22 : (1 : M2 n).toBlocks₂₂ = 1` using `by rw [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]`. Simplify using `[F0, f0, mR_one, u1, u2, h21, h22]`.
-/
theorem weight_factor_one (p q : ℕ) (e : ℤ) : F0 p q e (1 : GR n) = 1 := by
  have h21 : (1 : M2 n).toBlocks₂₁ = 0 := by rw [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₁]
  have h22 : (1 : M2 n).toBlocks₂₂ = 1 := by rw [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]
  simp [F0, f0, mR_one, u1, u2, h21, h22]

/- English proof (translation)
Simplify using `only [F0, f0, mR_mul, Matrix.det_mul, automorphy_first_mul_parabolic _ _ h, automorphy_second_mul_parabolic _ _ h, automorphy_first_parabolic _ h, automorphy_second_parabolic _ h, mul_zpow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weight_factor_mul_parabolic (p q : ℕ) (e : ℤ) (y g : GR n) (h : (mR y).toBlocks₂₁ = 0) :
    F0 p q e (y * g) = F0 p q e y * F0 p q e g := by
  simp only [F0, f0, mR_mul, Matrix.det_mul, automorphy_first_mul_parabolic _ _ h, automorphy_second_mul_parabolic _ _ h, automorphy_first_parabolic _ h, automorphy_second_parabolic _ h, mul_zpow]
  ring

/- English proof (translation)
Establish `hm : mR (mG a * nG b) = Matrix.fromBlocks a (a * b) 0 (aᴴ)⁻¹`. Rewrite using `[mR_mul, mR_mG ha, mR_nG hb, mLc, nU, Matrix.fromBlocks_multiply]`. Simplify using the standard rewrite rules. Establish `hs : star a.det ≠ 0` using `star_ne_zero.2 ha.ne_zero`. Establish `hi : ((aᴴ)⁻¹).det = (star a.det)⁻¹` using `by rw [Matrix.det_nonsing_inv, Matrix.det_conjTranspose, Ring.inverse_eq_inv']`.

Simplify using `only [F0, f0, hm, u1, u2, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, smul_zero, neg_zero, zero_add, Matrix.det_fromBlocks_zero₂₁, hi]`. Rewrite using `[mul_zpow, inv_zpow', inv_zpow', inv_zpow', neg_neg, neg_neg, mul_assoc, ← zpow_add₀ hs, ← zpow_add₀ hs]`. Put the polynomial expressions in normal form.
-/
theorem weight_factor_levi_unipotent (p q : ℕ) (e : ℤ) (a b : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) (hb : bᴴ = b) :
    F0 (n := n) p q e (mG a * nG b) = a.det ^ e * (star a.det) ^ ((p : ℤ) + q - e) := by
  have hm : mR (mG a * nG b) = Matrix.fromBlocks a (a * b) 0 (aᴴ)⁻¹ := by
    rw [mR_mul, mR_mG ha, mR_nG hb, mLc, nU, Matrix.fromBlocks_multiply]; simp
  have hs : star a.det ≠ 0 := star_ne_zero.2 ha.ne_zero
  have hi : ((aᴴ)⁻¹).det = (star a.det)⁻¹ := by rw [Matrix.det_nonsing_inv, Matrix.det_conjTranspose, Ring.inverse_eq_inv']
  simp only [F0, f0, hm, u1, u2, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, smul_zero, neg_zero,
    zero_add, Matrix.det_fromBlocks_zero₂₁, hi]
  rw [mul_zpow, inv_zpow', inv_zpow', inv_zpow', neg_neg, neg_neg, mul_assoc, ← zpow_add₀ hs, ← zpow_add₀ hs]
  ring_nf

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem mR_cont : Continuous (mR : GR n → M2 n) := Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
The claim follows from `continuous_pi fun i => continuous_pi fun j => (continuous_apply (g j)).comp (continuous_apply (f i))`.
-/
theorem cont_blk (f g : Fin n → Fin n ⊕ Fin n) : Continuous fun M : M2 n => (Matrix.of fun i j => M (f i) (g j)) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply (g j)).comp (continuous_apply (f i))

/- English proof (translation)
Establish `h21 : Continuous fun g : GR n => (mR g).toBlocks₂₁` using `(cont_blk Sum.inr Sum.inl).comp mR_cont`. Establish `h22 : Continuous fun g : GR n => (mR g).toBlocks₂₂` using `(cont_blk Sum.inr Sum.inr).comp mR_cont`. Establish `hd : Continuous fun g : GR n => (mR g).det` using `mR_cont.matrix_det`. Establish `hu1 : Continuous fun g : GR n => (u1 (mR g)).det` using `((h21.const_smul Complex.I).add h22).matrix_det`. Establish `hu2 : Continuous fun g : GR n => (u2 (mR g)).det` using `((h21.const_smul Complex.I).neg.add h22).matrix_det`.

Use `(hd.zpow₀ e fun g => Or.inl (det_ne_of_inG g.2).ne_zero).mul ?_` and prove the remaining obligations. Conclude with `(hu1.zpow₀ _ fun g => Or.inl (automorphy_first_det_ne_zero g)).mul (hu2.zpow₀ _ fun g => Or.inl (automorphy_second_det_ne_zero g))`.
-/
theorem continuous_weight_factor_unitary (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) := by
  have h21 : Continuous fun g : GR n => (mR g).toBlocks₂₁ := (cont_blk Sum.inr Sum.inl).comp mR_cont
  have h22 : Continuous fun g : GR n => (mR g).toBlocks₂₂ := (cont_blk Sum.inr Sum.inr).comp mR_cont
  have hd : Continuous fun g : GR n => (mR g).det := mR_cont.matrix_det
  have hu1 : Continuous fun g : GR n => (u1 (mR g)).det := ((h21.const_smul Complex.I).add h22).matrix_det
  have hu2 : Continuous fun g : GR n => (u2 (mR g)).det := ((h21.const_smul Complex.I).neg.add h22).matrix_det
  refine (hd.zpow₀ e fun g => Or.inl (det_ne_of_inG g.2).ne_zero).mul ?_
  exact (hu1.zpow₀ _ fun g => Or.inl (automorphy_first_det_ne_zero g)).mul (hu2.zpow₀ _ fun g => Or.inl (automorphy_second_det_ne_zero g))

/- English proof (translation)
Establish `hM` using `det_ne_of_inG h`. Establish `hX : IsUnit (JJ n * M).det`. Rewrite using `[Matrix.det_mul]`. Conclude with `(isUnit_iff_ne_zero.2 JJ_det_ne).mul hM`. Establish `e : M * JJ n * Mᴴ * (JJ n * M) = JJ n * (JJ n * M)`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inG_swap {M : M2 n} (h : InG M) : M * JJ n * Mᴴ = JJ n := by
  have hM := det_ne_of_inG h
  have hX : IsUnit (JJ n * M).det := by
    rw [Matrix.det_mul]; exact (isUnit_iff_ne_zero.2 JJ_det_ne).mul hM
  have e : M * JJ n * Mᴴ * (JJ n * M) = JJ n * (JJ n * M) := by
    calc M * JJ n * Mᴴ * (JJ n * M) = M * JJ n * (Mᴴ * JJ n * M) := by simp only [Matrix.mul_assoc]
      _ = M * (JJ n * JJ n) := by rw [h, Matrix.mul_assoc]
      _ = JJ n * (JJ n * M) := by rw [JJ_mul_JJ, ← Matrix.mul_assoc, JJ_mul_JJ]; simp
  calc M * JJ n * Mᴴ = M * JJ n * Mᴴ * ((JJ n * M) * (JJ n * M)⁻¹) := by rw [Matrix.mul_nonsing_inv _ hX, Matrix.mul_one]
    _ = JJ n * (JJ n * M) * (JJ n * M)⁻¹ := by rw [← Matrix.mul_assoc, e]
    _ = JJ n := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one]

/- English proof (translation)
Establish `e : Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ * JJ n * (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂)ᴴ = JJ n`. Rewrite using `[Matrix.fromBlocks_toBlocks]`. Conclude with `inG_swap h`. Simplify using `only [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at e`. Take `⟨-, e2, -, e4⟩` from `e`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `e2` as an intermediate fact. Simplify using `at this`. Rewrite using `[sub_eq_neg_add]`. Conclude with `this`.

Use `e4` as an intermediate fact. Simplify using `at this`. Conclude with `(neg_add_eq_zero.1 this).symm`.
-/
theorem inG_blocks' {M : M2 n} (h : InG M) :
    M.toBlocks₁₁ * M.toBlocks₂₂ᴴ - M.toBlocks₁₂ * M.toBlocks₂₁ᴴ = 1 ∧
    M.toBlocks₂₁ * M.toBlocks₂₂ᴴ = M.toBlocks₂₂ * M.toBlocks₂₁ᴴ := by
  have e : Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ * JJ n *
      (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂)ᴴ = JJ n := by
    rw [Matrix.fromBlocks_toBlocks]; exact inG_swap h
  simp only [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at e
  obtain ⟨-, e2, -, e4⟩ := e
  refine ⟨?_, ?_⟩
  · have := e2; simp at this; rw [sub_eq_neg_add]; exact this
  · have := e4; simp at this; exact (neg_add_eq_zero.1 this).symm

/- English proof (translation)
Take `⟨h1, -, -⟩` from `inG_blocks (M := mR g) g.2`. Take `⟨k2, k4⟩` from `inG_blocks' (M := mR g) g.2`. Use `set A := (mR g).toBlocks₁₁ with hA`. Use `set B := (mR g).toBlocks₁₂ with hB`. Use `set C := (mR g).toBlocks₂₁ with hC`.

Use `set D := (mR g).toBlocks₂₂ with hD`. Establish `hCi : C * C⁻¹ = 1` using `Matrix.mul_nonsing_inv _ h`. Establish `hiC : C⁻¹ * C = 1` using `Matrix.nonsing_inv_mul _ h`. Establish `hCH : (C⁻¹)ᴴ * Cᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, hCi, Matrix.conjTranspose_one]`. Establish `hHC : Cᴴ * (C⁻¹)ᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, hiC, Matrix.conjTranspose_one]`.

Use `set a := -(C⁻¹)ᴴ with ha_def`. Establish `ha : IsUnit a.det`. Establish `e : a * (-Cᴴ) = 1` using `by rw [ha_def, neg_mul_neg, hCH]`. Use `congrArg Matrix.det e` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_one]`.

Conclude with `isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one this)`. Establish `haH : (aᴴ)⁻¹ = -C`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[ha_def, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, neg_mul_neg, hCi]`. Establish `hb : (Cᴴ * A)ᴴ = Cᴴ * A` using `by rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h1]`.

Establish `hb' : (C⁻¹ * D)ᴴ = C⁻¹ * D`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨a, Cᴴ * A, C⁻¹ * D, ha, hb, hb', mR_injective ?_⟩` and prove the remaining obligations. Establish `hBe : B = A * (C⁻¹ * D) - (C⁻¹)ᴴ`.

Establish `hDC : Dᴴ * (C⁻¹)ᴴ = C⁻¹ * D` using `by rw [← Matrix.conjTranspose_mul, hb']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mR_mul, mR_mul, mR_mul, mR_mG ha, mR_nG hb, mR_jG, mR_nG hb', mLc, nU, JJ, nU, haH]`. Use `conv_lhs => rw [← Matrix.fromBlocks_toBlocks (mR g)]`. Simplify using `only [Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, neg_zero, neg_neg]`.

Rewrite using `[Matrix.fromBlocks_inj]`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;> symm`. Rewrite using `[ha_def, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, hCH, Matrix.one_mul]`. Rewrite using `[show Matrix.toBlocks₁₂ (mR g) = B from rfl, hBe, ha_def]`. Simplify using `only [Matrix.neg_mul, Matrix.mul_add, Matrix.mul_neg, ← Matrix.mul_assoc, hCH, Matrix.one_mul]`.

Normalize the expressions using the abelian group laws. Both sides reduce to the same expression. Rewrite using `[← Matrix.mul_assoc, hCi, Matrix.one_mul]`.
-/
theorem big_eq (g : GR n) (h : IsUnit (mR g).toBlocks₂₁.det) :
    ∃ a b b' : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ bᴴ = b ∧ b'ᴴ = b' ∧ g = mG a * nG b * jG n * nG b' := by
  obtain ⟨h1, -, -⟩ := inG_blocks (M := mR g) g.2
  obtain ⟨k2, k4⟩ := inG_blocks' (M := mR g) g.2
  set A := (mR g).toBlocks₁₁ with hA
  set B := (mR g).toBlocks₁₂ with hB
  set C := (mR g).toBlocks₂₁ with hC
  set D := (mR g).toBlocks₂₂ with hD
  have hCi : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have hiC : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul _ h
  have hCH : (C⁻¹)ᴴ * Cᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hCi, Matrix.conjTranspose_one]
  have hHC : Cᴴ * (C⁻¹)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hiC, Matrix.conjTranspose_one]
  set a := -(C⁻¹)ᴴ with ha_def
  have ha : IsUnit a.det := by
    have e : a * (-Cᴴ) = 1 := by rw [ha_def, neg_mul_neg, hCH]
    have := congrArg Matrix.det e
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one this)
  have haH : (aᴴ)⁻¹ = -C := by
    apply Matrix.inv_eq_left_inv
    rw [ha_def, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, neg_mul_neg, hCi]
  have hb : (Cᴴ * A)ᴴ = Cᴴ * A := by rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h1]
  have hb' : (C⁻¹ * D)ᴴ = C⁻¹ * D := by
    rw [Matrix.conjTranspose_mul]
    calc Dᴴ * (C⁻¹)ᴴ = C⁻¹ * (C * Dᴴ) * (C⁻¹)ᴴ := by rw [← Matrix.mul_assoc C⁻¹, hiC, Matrix.one_mul]
      _ = C⁻¹ * D * (Cᴴ * (C⁻¹)ᴴ) := by rw [k4]; simp only [Matrix.mul_assoc]
      _ = C⁻¹ * D := by rw [hHC, Matrix.mul_one]
  refine ⟨a, Cᴴ * A, C⁻¹ * D, ha, hb, hb', mR_injective ?_⟩
  have hBe : B = A * (C⁻¹ * D) - (C⁻¹)ᴴ := by
    have hDC : Dᴴ * (C⁻¹)ᴴ = C⁻¹ * D := by rw [← Matrix.conjTranspose_mul, hb']
    calc B = B * (Cᴴ * (C⁻¹)ᴴ) := by rw [hHC, Matrix.mul_one]
      _ = (A * Dᴴ - 1) * (C⁻¹)ᴴ := by rw [← Matrix.mul_assoc, ← k2]; abel_nf
      _ = A * (C⁻¹ * D) - (C⁻¹)ᴴ := by rw [Matrix.sub_mul, Matrix.mul_assoc, hDC, Matrix.one_mul]
  rw [mR_mul, mR_mul, mR_mul, mR_mG ha, mR_nG hb, mR_jG, mR_nG hb', mLc, nU, JJ, nU, haH]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (mR g)]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, neg_zero, neg_neg]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> symm
  · rw [ha_def, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, hCH, Matrix.one_mul]
  · rw [show Matrix.toBlocks₁₂ (mR g) = B from rfl, hBe, ha_def]; simp only [Matrix.neg_mul, Matrix.mul_add, Matrix.mul_neg, ← Matrix.mul_assoc, hCH, Matrix.one_mul]
    abel
  · rfl
  · rw [← Matrix.mul_assoc, hCi, Matrix.one_mul]

/- English proof (translation)
Use `⟨((Polynomial.X : Polynomial ℂ) • C.map Polynomial.C + D.map Polynomial.C).det, fun r => ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.coe_evalRingHom, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_poly (C D : Matrix (Fin n) (Fin n) ℂ) :
    ∃ p : Polynomial ℂ, ∀ r : ℂ, p.eval r = (r • C + D).det := by
  refine ⟨((Polynomial.X : Polynomial ℂ) • C.map Polynomial.C + D.map Polynomial.C).det, fun r => ?_⟩
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp
  ring

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hp` to reduce the goal to its premises. Apply `Polynomial.eq_zero_of_infinite_isRoot` to reduce the goal to its premises. Use `Set.Infinite.mono (fun x hx => ?_) (Set.infinite_range_of_injective (Nat.cast_injective (R := ℂ)))` and prove the remaining obligations.

Take `⟨k, rfl⟩` from `hx`. Conclude with `h k`.
-/
theorem exists_real_ne {p : Polynomial ℂ} (hp : p ≠ 0) : ∃ k : ℕ, p.eval (k : ℂ) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hp
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.Infinite.mono (fun x hx => ?_) (Set.infinite_range_of_injective (Nat.cast_injective (R := ℂ)))
  obtain ⟨k, rfl⟩ := hx
  exact h k

/- English proof (translation)
Establish `hi : ((-1 : Matrix (Fin n) (Fin n) ℂ)ᴴ)⁻¹ = -1`. Rewrite using `[Matrix.conjTranspose_neg, Matrix.conjTranspose_one]`. Conclude with `Matrix.inv_eq_left_inv (by simp)`. Rewrite using `[mLc, hi, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]`. Simplify using the standard rewrite rules.
-/
theorem mLc_neg_one : mLc (-1 : Matrix (Fin n) (Fin n) ℂ) = -1 := by
  have hi : ((-1 : Matrix (Fin n) (Fin n) ℂ)ᴴ)⁻¹ = -1 := by
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_one]
    exact Matrix.inv_eq_left_inv (by simp)
  rw [mLc, hi, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

/- English proof (translation)
Rewrite using `[Matrix.det_neg, Matrix.det_one, mul_one]`. Conclude with `(isUnit_neg_one.pow _)`.
-/
theorem isUnit_neg_one_det : IsUnit (-1 : Matrix (Fin n) (Fin n) ℂ).det := by
  rw [Matrix.det_neg, Matrix.det_one, mul_one]; exact (isUnit_neg_one.pow _)

/- English proof (translation)
Apply `mR_injective` to reduce the goal to its premises. Rewrite using `[mR_mul, mR_mul, mR_jG, mR_mG isUnit_neg_one_det, mLc_neg_one, JJ_mul_JJ, mR_one]`. Simplify using the standard rewrite rules.
-/
theorem jj_m_eq : jG n * jG n * mG (-1) = 1 := by
  apply mR_injective
  rw [mR_mul, mR_mul, mR_jG, mR_mG isUnit_neg_one_det, mLc_neg_one, JJ_mul_JJ, mR_one]
  simp

/- English proof (translation)
Rewrite using `[Matrix.conjTranspose_smul, Matrix.conjTranspose_one]`. Simplify using the standard rewrite rules.
-/
theorem herm_real (t : ℝ) : ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (t : ℂ) • 1 := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]; simp

/- English proof (translation)
Take `⟨p, hp⟩` from `det_poly (mR g).toBlocks₂₁ (mR g).toBlocks₂₂`. Establish `hp0 : p ≠ 0` using `fun h0 => automorphy_first_det_ne_zero g (by rw [u1, ← hp, h0, Polynomial.eval_zero])`. Take `⟨k, hk⟩` from `exists_real_ne hp0`. Use `set t : ℝ := (k : ℝ)`. Use `set g' := g * nG ((t : ℂ) • 1) * jG n`.

Establish `h21 : (mR g').toBlocks₂₁ = -((t : ℂ) • (mR g).toBlocks₂₁ + (mR g).toBlocks₂₂)`. Simplify using `only [g', mR_mul, mR_jG, mR_nG (herm_real t), lower_left_block_mul, lower_right_block_mul, JJ, nU, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]`. Simplify using `[Matrix.mul_smul, add_comm]`. Establish `hu : IsUnit (mR g').toBlocks₂₁.det`. Rewrite using `[h21, Matrix.det_neg, ← hp]`.

Conclude with `(isUnit_neg_one.pow _).mul (isUnit_iff_ne_zero.2 (by simpa [t] using hk))`. Take `⟨a, b, b', ha, hb, hb', hg'⟩` from `big_eq g' hu`. Use `⟨a, b, b', -t, ha, hb, hb', ?_⟩` and prove the remaining obligations. Rewrite using `[← hg']`. Simplify using `only [g', mul_assoc]`.

Establish `e0 : nG ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) * nG (((-t : ℝ) : ℂ) • 1) = 1`. Apply `mR_injective` to reduce the goal to its premises. Rewrite using `[mR_mul, mR_nG (herm_real t), mR_nG (herm_real (-t)), nU, nU, Matrix.fromBlocks_multiply, mR_one, ← Matrix.fromBlocks_one]`. Simplify using the standard rewrite rules. Establish `key : ∀ x : GR n, jG n * (jG n * (mG (-1) * x)) = x` using `fun x => by`.

Rewrite using `[← mul_assoc, ← mul_assoc, jj_m_eq, one_mul]`. Rewrite using `[key, e0, mul_one]`.
-/
theorem all_eq (g : GR n) :
    ∃ (a b b' : Matrix (Fin n) (Fin n) ℂ) (t : ℝ), IsUnit a.det ∧ bᴴ = b ∧ b'ᴴ = b' ∧
      g = mG a * nG b * jG n * nG b' * jG n * mG (-1) * nG ((t : ℂ) • 1) := by
  obtain ⟨p, hp⟩ := det_poly (mR g).toBlocks₂₁ (mR g).toBlocks₂₂
  have hp0 : p ≠ 0 := fun h0 => automorphy_first_det_ne_zero g (by rw [u1, ← hp, h0, Polynomial.eval_zero])
  obtain ⟨k, hk⟩ := exists_real_ne hp0
  set t : ℝ := (k : ℝ)
  set g' := g * nG ((t : ℂ) • 1) * jG n
  have h21 : (mR g').toBlocks₂₁ = -((t : ℂ) • (mR g).toBlocks₂₁ + (mR g).toBlocks₂₂) := by
    simp only [g', mR_mul, mR_jG, mR_nG (herm_real t), lower_left_block_mul, lower_right_block_mul, JJ, nU, Matrix.toBlocks_fromBlocks₁₁,
      Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
    simp [Matrix.mul_smul, add_comm]
  have hu : IsUnit (mR g').toBlocks₂₁.det := by
    rw [h21, Matrix.det_neg, ← hp]
    exact (isUnit_neg_one.pow _).mul (isUnit_iff_ne_zero.2 (by simpa [t] using hk))
  obtain ⟨a, b, b', ha, hb, hb', hg'⟩ := big_eq g' hu
  refine ⟨a, b, b', -t, ha, hb, hb', ?_⟩
  rw [← hg']
  simp only [g', mul_assoc]
  have e0 : nG ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) * nG (((-t : ℝ) : ℂ) • 1) = 1 := by
    apply mR_injective
    rw [mR_mul, mR_nG (herm_real t), mR_nG (herm_real (-t)), nU, nU, Matrix.fromBlocks_multiply, mR_one,
      ← Matrix.fromBlocks_one]
    simp
  have key : ∀ x : GR n, jG n * (jG n * (mG (-1) * x)) = x := fun x => by
    rw [← mul_assoc, ← mul_assoc, jj_m_eq, one_mul]
  rw [key, e0, mul_one]

/- English proof (translation)
Simplify using `[InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hc]`.
-/
theorem inG_nb {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) : InG (Matrix.fromBlocks 1 0 c 1) := by
  simp [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hc]

def nbG (t : ℝ) : GR n := toGR _ (inG_nb (herm_real (n := n) t))

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]`. Simplify using the standard rewrite rules.
-/
theorem nbG_inv_val (t : ℝ) :
    (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ =
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 (((-t : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  simp

/- English proof (translation)
Establish `h1 : Continuous fun t : ℝ => Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ)` using `Continuous.matrix_fromBlocks continuous_const continuous_const (Complex.continuous_ofReal.smul continuous_const) continuous_const`. Establish `h2 : Continuous fun t : ℝ => Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 (((-t : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ)` using `Continuous.matrix_fromBlocks continuous_const continuous_const ((Complex.continuous_ofReal.comp continuous_neg).smul continuous_const) continuous_const`. Use `Continuous.subtype_mk (Units.continuous_iff.2 ⟨h1, ?_⟩) _` and prove the remaining obligations. Use `h2.congr fun t => ?_` and prove the remaining obligations. Conclude with `(nbG_inv_val t).symm`.
-/
theorem nbG_cont : Continuous (nbG (n := n)) := by
  have h1 : Continuous fun t : ℝ => Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) :=
    Continuous.matrix_fromBlocks continuous_const continuous_const
      (Complex.continuous_ofReal.smul continuous_const) continuous_const
  have h2 : Continuous fun t : ℝ => Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 (((-t : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) :=
    Continuous.matrix_fromBlocks continuous_const continuous_const
      ((Complex.continuous_ofReal.comp continuous_neg).smul continuous_const) continuous_const
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨h1, ?_⟩) _
  refine h2.congr fun t => ?_
  exact (nbG_inv_val t).symm

/- English proof (translation)
Apply `mR_injective` to reduce the goal to its premises. Rewrite using `[mR_one, ← Matrix.fromBlocks_one]`. Use `show Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 (((0 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) = _`. Simplify using the standard rewrite rules.
-/
theorem nbG_zero : nbG (n := n) 0 = 1 := by
  apply mR_injective
  rw [mR_one, ← Matrix.fromBlocks_one]
  show Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 (((0 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) = _
  simp

/- English proof (translation)
Introduce `g`. Take `⟨p, hp⟩` from `det_poly (mR g).toBlocks₂₂ (mR g).toBlocks₂₁`. Establish `hp0 : p ≠ 0`. Introduce `h0`. Establish `e` using `hp (-Complex.I)`.

Rewrite `e` using `[h0, Polynomial.eval_zero]`. Establish `: (-Complex.I) • (mR g).toBlocks₂₂ + (mR g).toBlocks₂₁ = (-Complex.I) • u1 (mR g)`. Rewrite using `[u1, smul_add, smul_smul]`. Simplify using `[add_comm]`. Rewrite `e` using `[this, Matrix.det_smul]`.

Conclude with `mul_ne_zero (pow_ne_zero _ (by simp)) (automorphy_first_det_ne_zero g) e.symm`. Use `set S : Set ℝ := {t | p.eval (t : ℂ) = 0}`. Establish `hS : S.Finite`. Use `Set.Finite.subset ((p.roots.toFinset.finite_toSet).preimage Complex.ofReal_injective.injOn) fun t ht => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]`.

Conclude with `(Polynomial.mem_roots hp0).2 ht`. Establish `hd : Dense Sᶜ` using `hS.countable.dense_compl ℝ`. Establish `: Filter.NeBot (nhdsWithin (0 : ℝ) Sᶜ)` using `mem_closure_iff_nhdsWithin_neBot.1 (hd 0)`. Use `mem_closure_of_tendsto (f := fun t => g * nbG t) (b := nhdsWithin (0 : ℝ) Sᶜ) ?_ ?_` and prove the remaining obligations. Establish `: Continuous fun t => g * nbG (n` using `n) t := continuous_const.mul nbG_cont`.

Establish `h0` using `this.tendsto 0`. Simplify using `only [nbG_zero, mul_one] at h0`. Conclude with `h0.mono_left nhdsWithin_le_nhds`. Use `eventually_nhdsWithin_of_forall fun t ht => ?_ show IsUnit (mR (g * nbG t)).toBlocks₂₁.det` and prove the remaining obligations. Establish `e : (mR (g * nbG t)).toBlocks₂₁ = (t : ℂ) • (mR g).toBlocks₂₂ + (mR g).toBlocks₂₁`.

Rewrite using `[mR_mul, lower_left_block_mul]`. Use `show _ * (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ)).toBlocks₁₁ + _ * (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ)). …`. Simplify using `[add_comm]`. Rewrite using `[e, ← hp]`. Conclude with `isUnit_iff_ne_zero.2 ht`.
-/
theorem dense_big : Dense {g : GR n | IsUnit (mR g).toBlocks₂₁.det} := by
  intro g
  obtain ⟨p, hp⟩ := det_poly (mR g).toBlocks₂₂ (mR g).toBlocks₂₁
  have hp0 : p ≠ 0 := by
    intro h0
    have e := hp (-Complex.I)
    rw [h0, Polynomial.eval_zero] at e
    have : (-Complex.I) • (mR g).toBlocks₂₂ + (mR g).toBlocks₂₁ = (-Complex.I) • u1 (mR g) := by
      rw [u1, smul_add, smul_smul]; simp [add_comm]
    rw [this, Matrix.det_smul] at e
    exact mul_ne_zero (pow_ne_zero _ (by simp)) (automorphy_first_det_ne_zero g) e.symm
  set S : Set ℝ := {t | p.eval (t : ℂ) = 0}
  have hS : S.Finite := by
    refine Set.Finite.subset ((p.roots.toFinset.finite_toSet).preimage Complex.ofReal_injective.injOn) fun t ht => ?_
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_roots hp0).2 ht
  have hd : Dense Sᶜ := hS.countable.dense_compl ℝ
  have : Filter.NeBot (nhdsWithin (0 : ℝ) Sᶜ) := mem_closure_iff_nhdsWithin_neBot.1 (hd 0)
  refine mem_closure_of_tendsto (f := fun t => g * nbG t) (b := nhdsWithin (0 : ℝ) Sᶜ) ?_ ?_
  · have : Continuous fun t => g * nbG (n := n) t := continuous_const.mul nbG_cont
    have h0 := this.tendsto 0
    simp only [nbG_zero, mul_one] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  · refine eventually_nhdsWithin_of_forall fun t ht => ?_
    show IsUnit (mR (g * nbG t)).toBlocks₂₁.det
    have e : (mR (g * nbG t)).toBlocks₂₁ = (t : ℂ) • (mR g).toBlocks₂₂ + (mR g).toBlocks₂₁ := by
      rw [mR_mul, lower_left_block_mul]
      show _ * (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ)).toBlocks₁₁ +
        _ * (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ)).toBlocks₂₁ = _
      simp [add_comm]
    rw [e, ← hp]
    exact isUnit_iff_ne_zero.2 ht

end PositivityTheory.SiegelWeilFormula.KLI

end
