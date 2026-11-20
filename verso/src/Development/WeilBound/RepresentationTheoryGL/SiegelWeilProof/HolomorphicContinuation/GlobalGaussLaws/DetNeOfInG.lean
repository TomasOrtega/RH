import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussSt

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.VacB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[JJ, fromBlocks_multiply]`. Simplify using `only [Matrix.zero_mul, Matrix.one_mul, Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.neg_mul, Matrix.mul_neg]`. Rewrite using `[← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]`.
-/
theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.one_mul, Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero,
    Matrix.neg_mul, Matrix.mul_neg]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]

/- English proof (translation)
Introduce `h`. Use `congrArg Matrix.det (JJ_mul_JJ (n := n))` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h, zero_mul, Matrix.det_neg]`. Simplify using `at this`.
-/
theorem det_JJ_ne : (JJ n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (JJ_mul_JJ (n := n))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_neg] at this
  simp at this

/- English proof (translation)
Introduce `h0`. Use `congrArg Matrix.det h` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_mul, h0, mul_zero]`. Conclude with `det_JJ_ne this.symm`.
-/
theorem det_ne_of_inG {g : M2 n} (h : InG g) : g.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact det_JJ_ne this.symm

def mkG (g : M2 n) (h : InG g) : GR n := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g (det_ne_of_inG h), h⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem mR_mkG (g : M2 n) (h : InG g) : mR (mkG g h) = g := rfl

/- English proof (translation)
Simplify using `[InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]`.
-/
theorem inG_nU (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) : InG (nU b) := by
  simp [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]

/- English proof (translation)
Simplify using `[InG, nbar, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hc]`.
-/
theorem inG_nbar (c : Matrix (Fin n) (Fin n) ℂ) (hc : cᴴ = c) : InG (nbar c) := by
  simp [InG, nbar, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hc]

/- English proof (translation)
Establish `hu : IsUnit aᴴ.det`. Rewrite using `[Matrix.det_conjTranspose]`. Conclude with `ha.star`. Simplify using `[InG, mM, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_nonsing_inv, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ ha]`.
-/
theorem inG_mM (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) : InG (mM a) := by
  have hu : IsUnit aᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact ha.star
  simp [InG, mM, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_nonsing_inv, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ ha]

def kth (θ : Fin n → ℝ) : M2 n :=
  fromBlocks (diagonal fun j => (Real.cos (θ j) : ℂ)) (diagonal fun j => (Real.sin (θ j) : ℂ))
    (-diagonal fun j => (Real.sin (θ j) : ℂ)) (diagonal fun j => (Real.cos (θ j) : ℂ))

/- English proof (translation)
Establish `hcs : ∀ j : Fin n, (Real.cos (θ j) : ℂ) * Real.cos (θ j) + (Real.sin (θ j) : ℂ) * Real.sin (θ j) = 1`. Introduce `j`. Rewrite using `[← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]`. Rewrite using `[← sq, ← sq, Real.cos_sq_add_sin_sq, Complex.ofReal_one]`. Establish `hsc : ∀ j : Fin n, (Real.sin (θ j) : ℂ) * Real.sin (θ j) + (Real.cos (θ j) : ℂ) * Real.cos (θ j) = 1`.

Introduce `j`. Rewrite using `[add_comm]`. Conclude with `hcs j`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `[InG, kth, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, -Complex.ofReal_cos, -Complex.ofReal_sin, Complex.conj_ofReal, hcs, hsc]`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.zero_apply]`. Expand and normalize the polynomial expressions, which then agree. Use extensionality with `i j`.

Rewrite using `[Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply]`. Use `split_ifs`. Take the linear combination `-(hcs i)`. Simplify using the standard rewrite rules. Use function extensionality and compare the values at `i`.

Rewrite using `[Pi.zero_apply]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[kth, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, -Complex.ofReal_cos, -Complex.ofReal_sin, Complex.conj_ofReal, hcs, hsc]`. Establish `h0 : (Matrix.diagonal fun i : Fin n => (Real.cos (θ i) : ℂ) * Real.sin (θ i) + -((Real.sin (θ i) : ℂ) * Real.cos (θ i))) = 0`. Rewrite using `[← Matrix.diagonal_zero]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : (Matrix.diagonal fun i : Fin n => (Real.sin (θ i) : ℂ) * Real.cos (θ i) + -((Real.cos (θ i) : ℂ) * Real.sin (θ i))) = 0`. Rewrite using `[← Matrix.diagonal_zero]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h0, h1, Matrix.fromBlocks_one]`.
-/
theorem inK_kth (θ : Fin n → ℝ) : InK (kth θ) := by
  have hcs : ∀ j : Fin n, (Real.cos (θ j) : ℂ) * Real.cos (θ j) + (Real.sin (θ j) : ℂ) * Real.sin (θ j) = 1 := by
    intro j
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
    rw [← sq, ← sq, Real.cos_sq_add_sin_sq, Complex.ofReal_one]
  have hsc : ∀ j : Fin n, (Real.sin (θ j) : ℂ) * Real.sin (θ j) + (Real.cos (θ j) : ℂ) * Real.cos (θ j) = 1 := by
    intro j
    rw [add_comm]
    exact hcs j
  refine ⟨?_, ?_⟩
  · simp [InG, kth, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, -Complex.ofReal_cos,
      -Complex.ofReal_sin, Complex.conj_ofReal, hcs, hsc]
    refine ⟨?_, ?_, ?_⟩
    · funext i
      rw [Pi.zero_apply]
      ring
    · ext i j
      rw [Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply]
      split_ifs
      · linear_combination -(hcs i)
      · simp
    · funext i
      rw [Pi.zero_apply]
      ring
  · simp [kth, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, -Complex.ofReal_cos,
      -Complex.ofReal_sin, Complex.conj_ofReal, hcs, hsc]
    have h0 : (Matrix.diagonal fun i : Fin n => (Real.cos (θ i) : ℂ) * Real.sin (θ i) +
        -((Real.sin (θ i) : ℂ) * Real.cos (θ i))) = 0 := by
      rw [← Matrix.diagonal_zero]
      congr 1
      funext i
      ring
    have h1 : (Matrix.diagonal fun i : Fin n => (Real.sin (θ i) : ℂ) * Real.cos (θ i) +
        -((Real.cos (θ i) : ℂ) * Real.sin (θ i))) = 0 := by
      rw [← Matrix.diagonal_zero]
      congr 1
      funext i
      ring
    rw [h0, h1, Matrix.fromBlocks_one]

end PositivityTheory.Rg.Sw.Glob.VacB
