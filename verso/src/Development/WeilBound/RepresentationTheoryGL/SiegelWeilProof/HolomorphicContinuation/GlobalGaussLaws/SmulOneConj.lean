import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

namespace DRealH

variable {n : ℕ}

/- English proof (translation)
Establish `h` using `hg`. Unfold `InG JJ at h`. Rewrite `h` using `[← Matrix.fromBlocks_toBlocks g, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero, Matrix.fromBlocks_inj] at h`. Take `⟨h11, h12, h21, h22⟩` from `h`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `congrArg (· + (g.toBlocks₂₁)ᴴ * g.toBlocks₁₁) h11` as an intermediate fact. Simplify `this` using `[Matrix.mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]`. Use `congrArg (· + (g.toBlocks₂₂)ᴴ * g.toBlocks₁₂) h22` as an intermediate fact. Simplify `this` using `[Matrix.mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]`.

Simplify `h12` using `[Matrix.mul_assoc, sub_eq_add_neg, add_comm]`. Simplify `h21` using `[Matrix.mul_assoc, sub_eq_add_neg, add_comm]`.
-/
theorem blocks_of_inG {g : M2 n} (hg : InG g) :
    (g.toBlocks₁₁)ᴴ * g.toBlocks₂₁ = (g.toBlocks₂₁)ᴴ * g.toBlocks₁₁ ∧
    (g.toBlocks₁₂)ᴴ * g.toBlocks₂₂ = (g.toBlocks₂₂)ᴴ * g.toBlocks₁₂ ∧
    (g.toBlocks₁₁)ᴴ * g.toBlocks₂₂ - (g.toBlocks₂₁)ᴴ * g.toBlocks₁₂ = 1 ∧
    (g.toBlocks₁₂)ᴴ * g.toBlocks₂₁ - (g.toBlocks₂₂)ᴴ * g.toBlocks₁₁ = -1 := by
  have h := hg
  unfold InG JJ at h
  rw [← Matrix.fromBlocks_toBlocks g, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero,
    Matrix.fromBlocks_inj] at h
  obtain ⟨h11, h12, h21, h22⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrArg (· + (g.toBlocks₂₁)ᴴ * g.toBlocks₁₁) h11
    simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  · have := congrArg (· + (g.toBlocks₂₂)ᴴ * g.toBlocks₁₂) h22
    simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  · simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm] using h12
  · simpa [Matrix.mul_assoc, sub_eq_add_neg, add_comm] using h21

variable {A B C D : Matrix (Fin n) (Fin n) ℂ}

/- English proof (translation)
Rewrite using `[conjTranspose_smul, conjTranspose_one]`.
-/
theorem smul_one_conj (w : ℂ) : ((w • (1 : Matrix (Fin n) (Fin n) ℂ)))ᴴ = (star w) • 1 := by
  rw [conjTranspose_smul, conjTranspose_one]

/- English proof (translation)
Establish `e3 : Aᴴ * D = 1 + Cᴴ * B` using `by rw [← h3]; abel`. Establish `e4 : Bᴴ * C = -1 + Dᴴ * A` using `by rw [← h4]; abel`. Simplify using `only [conjTranspose_add, conjTranspose_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, e3, e4, h1, h2]`. Use `module`.
-/
theorem cross_self (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) : (w • A + B)ᴴ * (w • C + D) - (w • C + D)ᴴ * (w • A + B) = (star w - w) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have e3 : Aᴴ * D = 1 + Cᴴ * B := by rw [← h3]; abel
  have e4 : Bᴴ * C = -1 + Dᴴ * A := by rw [← h4]; abel
  simp only [conjTranspose_add, conjTranspose_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, e3, e4, h1, h2]
  module

/- English proof (translation)
Establish `e3 : Aᴴ * D = 1 + Cᴴ * B` using `eq_add_of_sub_eq h3`. Establish `e4 : Bᴴ * C = -1 + Dᴴ * A` using `eq_add_of_sub_eq h4`. Simplify using `only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]`. Rewrite using `[h1, h2, e3, e4]`. Use `module`.
-/
theorem cross_conj (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) : (w • A + B)ᴴ * ((star w) • C + D) = (w • C + D)ᴴ * ((star w) • A + B) := by
  have e3 : Aᴴ * D = 1 + Cᴴ * B := eq_add_of_sub_eq h3
  have e4 : Bᴴ * C = -1 + Dᴴ * A := eq_add_of_sub_eq h4
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul]
  rw [h1, h2, e3, e4]
  module

/- English proof (translation)
Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Establish `key` using `cross_self h1 h2 h3 h4 w`. Establish `e` using `congrArg (fun M => star v ⬝ᵥ (M *ᵥ v)) key`. Establish `l1 : ((w • A + B)ᴴ * (w • C + D) - (w • C + D)ᴴ * (w • A + B)) *ᵥ v = -((w • C + D)ᴴ *ᵥ ((w • A + B) *ᵥ v))`.

Rewrite using `[Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, zero_sub]`. Establish `l2 : ((star w - w) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v = (star w - w) • v`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.one_apply]`. Simplify using `only [l1, l2] at e`.

Rewrite `e` using `[dotProduct_neg, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hv, star_zero, zero_dotProduct, neg_zero, dotProduct_smul, smul_eq_mul]`. Establish `hne : star w - w ≠ 0` using `sub_ne_zero.mpr hw`. Establish `: star v ⬝ᵥ v = 0` using `(mul_eq_zero.mp e.symm).resolve_left hne`. Conclude with `hv0 (dotProduct_star_self_eq_zero.mp this)`.
-/
theorem det_ne_zero (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) (hw : star w ≠ w) : (w • C + D).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have key := cross_self h1 h2 h3 h4 w
  have e := congrArg (fun M => star v ⬝ᵥ (M *ᵥ v)) key
  have l1 : ((w • A + B)ᴴ * (w • C + D) - (w • C + D)ᴴ * (w • A + B)) *ᵥ v
      = -((w • C + D)ᴴ *ᵥ ((w • A + B) *ᵥ v)) := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, zero_sub]
  have l2 : ((star w - w) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v = (star w - w) • v := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  simp only [l1, l2] at e
  rw [dotProduct_neg, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hv, star_zero, zero_dotProduct, neg_zero,
    dotProduct_smul, smul_eq_mul] at e
  have hne : star w - w ≠ 0 := sub_ne_zero.mpr hw
  have : star v ⬝ᵥ v = 0 := (mul_eq_zero.mp e.symm).resolve_left hne
  exact hv0 (dotProduct_star_self_eq_zero.mp this)

/- English proof (translation)
Establish `hw' : star (star w) ≠ star w`. Rewrite using `[star_star]`. Conclude with `fun h => hw h.symm`. Establish `d1` using `det_ne_zero h1 h2 h3 h4 w hw`. Establish `d2` using `det_ne_zero h1 h2 h3 h4 (star w) hw'`.

Establish `u1 : IsUnit (w • C + D)ᴴ.det`. Rewrite using `[Matrix.det_conjTranspose]`. Conclude with `(star_ne_zero.mpr d1).isUnit`. Establish `u2 : IsUnit ((star w) • C + D).det` using `d2.isUnit`. Establish `cc` using `cross_conj h1 h2 h3 h4 w`.

Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ u2]`. Use `_ = ((w • C + D)ᴴ)⁻¹ * ((w • C + D)ᴴ * ((star w) • A + B)) * ((star w) • C + D)⁻¹ := by rw [cc]`. Use `_ = ((star w) • A + B) * ((star w) • C + D)⁻¹ := by`.

Rewrite using `[Matrix.nonsing_inv_mul_cancel_left _ _ u1]`.
-/
theorem conj_frac (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (w : ℂ) (hw : star w ≠ w) :
    ((w • A + B) * (w • C + D)⁻¹)ᴴ = ((star w) • A + B) * ((star w) • C + D)⁻¹ := by
  have hw' : star (star w) ≠ star w := by
    rw [star_star]
    exact fun h => hw h.symm
  have d1 := det_ne_zero h1 h2 h3 h4 w hw
  have d2 := det_ne_zero h1 h2 h3 h4 (star w) hw'
  have u1 : IsUnit (w • C + D)ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact (star_ne_zero.mpr d1).isUnit
  have u2 : IsUnit ((star w) • C + D).det := d2.isUnit
  have cc := cross_conj h1 h2 h3 h4 w
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
  calc ((w • C + D)ᴴ)⁻¹ * (w • A + B)ᴴ
      = ((w • C + D)ᴴ)⁻¹ * ((w • A + B)ᴴ * ((star w) • C + D)) * ((star w) • C + D)⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ u2]
    _ = ((w • C + D)ᴴ)⁻¹ * ((w • C + D)ᴴ * ((star w) • A + B)) * ((star w) • C + D)⁻¹ := by rw [cc]
    _ = ((star w) • A + B) * ((star w) • C + D)⁻¹ := by
        rw [Matrix.nonsing_inv_mul_cancel_left _ _ u1]

end DRealH

open DRealH in
/- English proof (translation)
Introduce `m n ε t c e y X a ha s`. Use function extensionality and compare the values at `u`. Establish `hA : aC X (s : ℂ) = mR (a s)`. Rewrite using `[ha s]`. Unfold `aC`.

Use `congr 1`. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[Complex.ofReal_exp, Complex.ofReal_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Rewrite using `[Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]`. Establish `hmul : mR y * aC X (s : ℂ) = mR (y * a s)`. Rewrite using `[hA]`. Both sides reduce to the same expression.

Establish `hG : InG (mR (y * a s))` using `(y * a s).2`. Take `⟨h1, h2, h3, h4⟩` from `blocks_of_inG hG`. Establish `hIs : star Complex.I ≠ Complex.I`. Rewrite using `[Complex.star_def, Complex.conj_I]`. Introduce `h`.

Use `congrArg Complex.im h` as an intermediate fact. Simplify using `at this`. Evaluate the numerical expressions using `at this`. Establish `key` using `conj_frac h1 h2 h3 h4 Complex.I hIs`. Establish `sI : star Complex.I = -Complex.I` using `by rw [Complex.star_def, Complex.conj_I]`.

Rewrite `key` using `[sI]`. Establish `cI : ((Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)))ᴴ = (-Complex.I) • 1`. Rewrite using `[smul_one_conj, sI]`. Unfold `famC jF gZf gC jC ptZ actZ`. Simplify using `only [hmul, cI, Matrix.mul_smul, Matrix.mul_one]`.

Rewrite using `[key]`.
-/
theorem dReal : DReal := by
  intro m n ε t c e y X a ha s
  funext u
  have hA : aC X (s : ℂ) = mR (a s) := by
    rw [ha s]
    unfold aC
    congr 1
    · congr 1
      funext j
      rw [Complex.ofReal_exp, Complex.ofReal_mul]
    · congr 1
      funext j
      rw [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
  have hmul : mR y * aC X (s : ℂ) = mR (y * a s) := by
    rw [hA]
    rfl
  have hG : InG (mR (y * a s)) := (y * a s).2
  obtain ⟨h1, h2, h3, h4⟩ := blocks_of_inG hG
  have hIs : star Complex.I ≠ Complex.I := by
    rw [Complex.star_def, Complex.conj_I]
    intro h
    have := congrArg Complex.im h
    simp at this
    norm_num at this
  have key := conj_frac h1 h2 h3 h4 Complex.I hIs
  have sI : star Complex.I = -Complex.I := by rw [Complex.star_def, Complex.conj_I]
  rw [sI] at key
  have cI : ((Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)))ᴴ = (-Complex.I) • 1 := by
    rw [smul_one_conj, sI]
  unfold famC jF gZf gC jC ptZ actZ
  simp only [hmul, cI, Matrix.mul_smul, Matrix.mul_one]
  rw [key]

end PositivityTheory.Rg.Sw.Glob
