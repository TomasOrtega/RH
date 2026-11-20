import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.CharacterW1TraceExp

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Use extensionality with `k l`. Rewrite using `[Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Distinguish the cases in `hk : k = i₀`. Substitute `hk` using the available equality. Rewrite using `[hr]`.

Simplify using the standard rewrite rules. Distinguish the cases in `hl : l = i₀`. Substitute `hl` using the available equality. Rewrite using `[hc]`. Simplify using the standard rewrite rules.

Rewrite using `[Pi.star_apply, hdv k hk, hdv l hl]`. Simplify using the standard rewrite rules.
-/
theorem stab_diag {n : ℕ} (i₀ : Fin n) (dv : Fin n → ℂ) (hdv : ∀ k, k ≠ i₀ → dv k = 1)
    (β : Matrix (Fin n) (Fin n) ℂ) (hr : ∀ l, β i₀ l = 0) (hc : ∀ k, β k i₀ = 0) :
    (Matrix.diagonal dv)ᴴ * β * Matrix.diagonal dv = β := by
  ext k l
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hk : k = i₀
  · subst hk; rw [hr]; simp
  · by_cases hl : l = i₀
    · subst hl; rw [hc]; simp
    · rw [Pi.star_apply, hdv k hk, hdv l hl]; simp

/- English proof (translation)
Establish `h1 : β * M = 0`. Use extensionality with `k l`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i₀]`. Rewrite using `[hc]`. Simplify using the standard rewrite rules.

Introduce `p _ hp`. Rewrite using `[hM p l hp, mul_zero]`. Simplify using the standard rewrite rules. Establish `h2 : Mᴴ * β = 0`. Use extensionality with `k l`.

Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i₀]`. Rewrite using `[hr]`. Simplify using the standard rewrite rules. Introduce `p _ hp`. Rewrite using `[Matrix.conjTranspose_apply, hM p k hp, star_zero, zero_mul]`.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]`. Simplify using `only [Matrix.one_mul, Matrix.mul_one, h1, h2, Matrix.zero_mul, add_zero]`.
-/
theorem stab_row {n : ℕ} (i₀ : Fin n) (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ k l, k ≠ i₀ → M k l = 0)
    (β : Matrix (Fin n) (Fin n) ℂ) (hr : ∀ l, β i₀ l = 0) (hc : ∀ k, β k i₀ = 0) :
    (1 + M)ᴴ * β * (1 + M) = β := by
  have h1 : β * M = 0 := by
    ext k l
    rw [Matrix.mul_apply, Finset.sum_eq_single i₀]
    · rw [hc]; simp
    · intro p _ hp; rw [hM p l hp, mul_zero]
    · simp
  have h2 : Mᴴ * β = 0 := by
    ext k l
    rw [Matrix.mul_apply, Finset.sum_eq_single i₀]
    · rw [hr]; simp
    · intro p _ hp; rw [Matrix.conjTranspose_apply, hM p k hp, star_zero, zero_mul]
    · simp
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.one_mul, Matrix.mul_one, h1, h2, Matrix.zero_mul, add_zero]

/- English proof (translation)
Establish `e : M = Matrix.replicateCol Unit (Pi.single i₀ (1 : ℂ)) * Matrix.replicateRow Unit (M i₀)`. Use extensionality with `k l`. Simplify using `only [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton]`. Distinguish the cases in `hk : k = i₀`. Substitute `hk` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[hM k l hk, Pi.single_eq_of_ne hk, zero_mul]`. Rewrite using `[e, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_single, h0, zero_mul, add_zero]`.
-/
theorem det_row {n : ℕ} (i₀ : Fin n) (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ k l, k ≠ i₀ → M k l = 0)
    (h0 : M i₀ i₀ = 0) : (1 + M).det = 1 := by
  have e : M = Matrix.replicateCol Unit (Pi.single i₀ (1 : ℂ)) * Matrix.replicateRow Unit (M i₀) := by
    ext k l
    simp only [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Finset.univ_unique,
      Finset.sum_singleton]
    by_cases hk : k = i₀
    · subst hk; simp
    · rw [hM k l hk, Pi.single_eq_of_ne hk, zero_mul]
  rw [e, Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_single, h0, zero_mul, add_zero]

/- English proof (translation)
Unfold `InG JJ at h`. Rewrite `h` using `[Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `at h`. Conclude with `h.1`.
-/
theorem blocks_of_inG {n : ℕ} (a a' : Matrix (Fin n) (Fin n) ℂ) (h : InG (Matrix.fromBlocks a 0 0 a')) : aᴴ * a' = 1 := by
  unfold InG JJ at h
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h
  simp at h
  exact h.1

/- English proof (translation)
Unfold `F0 f0 u1 u2`. Rewrite using `[hy, Matrix.det_fromBlocks_zero₂₁, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]`. Simplify using the standard rewrite rules.
-/
theorem weight_factor_blocks {n : ℕ} (pp qq : ℕ) (e : ℤ) (y : GR n) (a a' : Matrix (Fin n) (Fin n) ℂ)
    (hy : mR y = Matrix.fromBlocks a 0 0 a') :
    F0 pp qq e y = (a.det * a'.det) ^ e * (a'.det ^ (-(pp : ℤ)) * a'.det ^ (-(qq : ℤ))) := by
  unfold F0 f0 u1 u2
  rw [hy, Matrix.det_fromBlocks_zero₂₁, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  simp

/- English proof (translation)
Establish `hG : InG (Matrix.fromBlocks a 0 0 a')` using `hy ▸ y.2`. Establish `h1` using `congrArg Matrix.det (blocks_of_inG a a' hG)`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_conjTranspose, ha, star_one, one_mul, Matrix.det_one]`. Rewrite using `[weight_factor_blocks pp qq e y a a' hy, ha, h1]`. Simplify using the standard rewrite rules.
-/
theorem weight_factor_det_one {n : ℕ} (pp qq : ℕ) (e : ℤ) (y : GR n) (a a' : Matrix (Fin n) (Fin n) ℂ)
    (hy : mR y = Matrix.fromBlocks a 0 0 a') (ha : a.det = 1) : F0 pp qq e y = 1 := by
  have hG : InG (Matrix.fromBlocks a 0 0 a') := hy ▸ y.2
  have h1 := congrArg Matrix.det (blocks_of_inG a a' hG)
  rw [Matrix.det_mul, Matrix.det_conjTranspose, ha, star_one, one_mul, Matrix.det_one] at h1
  rw [weight_factor_blocks pp qq e y a a' hy, ha, h1]
  simp

/- English proof (translation)
Establish `hd1 : (Matrix.diagonal fun j => ((Real.exp (τ * (Pi.single i₀ (1 : ℝ) : Fin n → ℝ) j) : ℝ) : ℂ)).det = Complex.exp τ`. Rewrite using `[Matrix.det_diagonal, Finset.prod_eq_single i₀]`. Simplify using `[Complex.ofReal_exp]`. Introduce `j _ hj`. Simplify using `[Pi.single_eq_of_ne hj]`.

Simplify using the standard rewrite rules. Establish `hd2 : (Matrix.diagonal fun j => ((Real.exp (-(τ * (Pi.single i₀ (1 : ℝ) : Fin n → ℝ) j)) : ℝ) : ℂ)).det = Complex.exp (-τ)`. Rewrite using `[Matrix.det_diagonal, Finset.prod_eq_single i₀]`. Simplify using `[Complex.ofReal_exp]`. Introduce `j _ hj`.

Simplify using `[Pi.single_eq_of_ne hj]`. Simplify using the standard rewrite rules. Rewrite using `[weight_factor_blocks pp qq e y _ _ hy, hd1, hd2, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_zpow, one_mul]`. Rewrite using `[← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weight_factor_dilation {n : ℕ} (i₀ : Fin n) (τ : ℝ) (y : GR n) (hy : IsDil (Pi.single i₀ 1) τ y) (pp qq : ℕ) (e : ℤ) :
    F0 pp qq e y = Complex.exp (τ * ((pp + qq : ℕ) : ℂ)) := by
  have hd1 : (Matrix.diagonal fun j => ((Real.exp (τ * (Pi.single i₀ (1 : ℝ) : Fin n → ℝ) j) : ℝ) : ℂ)).det = Complex.exp τ := by
    rw [Matrix.det_diagonal, Finset.prod_eq_single i₀]
    · simp [Complex.ofReal_exp]
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  have hd2 : (Matrix.diagonal fun j => ((Real.exp (-(τ * (Pi.single i₀ (1 : ℝ) : Fin n → ℝ) j)) : ℝ) : ℂ)).det = Complex.exp (-τ) := by
    rw [Matrix.det_diagonal, Finset.prod_eq_single i₀]
    · simp [Complex.ofReal_exp]
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  rw [weight_factor_blocks pp qq e y _ _ hy, hd1, hd2, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_zpow, one_mul]
  rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end PositivityTheory.SiegelWeilFormula.AStep

end
