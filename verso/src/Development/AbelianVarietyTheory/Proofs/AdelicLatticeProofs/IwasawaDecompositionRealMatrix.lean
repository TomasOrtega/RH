import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Set `f : Fin N → EuclideanSpace ℝ (Fin N)` to `fun j => WithLp.toLp 2 (fun i => g i j)`. Establish `h : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = Fintype.card (Fin N)` using `by simp`. Set `b` to `InnerProductSpace.gramSchmidtOrthonormalBasis h f`. Use `⟨Matrix.of fun i j => b j i, Matrix.of fun i j => inner ℝ (b i) (f j), ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Use `orthonormal_iff_ite.mp b.orthonormal i j` as an intermediate fact. Rewrite using `[Matrix.mul_apply, Matrix.one_apply, ← this, PiLp.inner_apply]`. Simplify using `[mul_comm]`. Introduce `i j hij`. Conclude with `InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular h f hij`.

Use extensionality with `i j`. Use `congrArg (fun v : EuclideanSpace ℝ (Fin N) => v i) (b.sum_repr' (f j))` as an intermediate fact. Simplify using `only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at this`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_orthogonal_mul_upper (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ) :
    ∃ (k r : Matrix (Fin N) (Fin N) ℝ), kᵀ * k = 1 ∧ (∀ i j, j < i → r i j = 0) ∧ g = k * r := by
  classical
  let f : Fin N → EuclideanSpace ℝ (Fin N) := fun j => WithLp.toLp 2 (fun i => g i j)
  have h : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = Fintype.card (Fin N) := by simp
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis h f
  refine ⟨Matrix.of fun i j => b j i, Matrix.of fun i j => inner ℝ (b i) (f j), ?_, ?_, ?_⟩
  · ext i j
    have := orthonormal_iff_ite.mp b.orthonormal i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← this, PiLp.inner_apply]
    simp [mul_comm]
  · intro i j hij
    exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular h f hij
  · ext i j
    have := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v i) (b.sum_repr' (f j))
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    calc g i j = f j i := rfl
      _ = _ := this.symm
      _ = _ := Finset.sum_congr rfl fun x _ => mul_comm _ _

/- English proof (translation)
Introduce `N g hg`. Take `⟨k, r, hk, hr, rfl⟩` from `exists_orthogonal_mul_upper N g`. Establish `hbt : r.BlockTriangular id` using `fun i j hij => hr i j hij`. Establish `hdet : r.det ≠ 0`. Introduce `h0`.

Apply `hg` to reduce the goal to its premises. Rewrite using `[Matrix.det_mul, h0, mul_zero]`. Rewrite `hdet` using `[Matrix.det_of_isUpperTriangular hbt, Finset.prod_ne_zero_iff]`. Establish `hne : ∀ i, r i i ≠ 0` using `fun i => hdet i (Finset.mem_univ i)`. Establish `habs : ∀ i, |r i i| ≠ 0` using `fun i => abs_ne_zero.mpr (hne i)`.

Use `⟨k * diagonal (fun i => r i i / |r i i|), fun i => |r i i|, Matrix.of fun i j => r i j / r i i, ?_, fun i => abs_pos.mpr (hne i), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc kᵀ, hk, Matrix.one_mul, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[div_mul_div_comm, abs_mul_abs_self, div_self (mul_ne_zero (hne i) (hne i))]`.

Introduce `i`. Conclude with `div_self (hne i)`. Introduce `i j hij`. Simplify using `[hr i j hij]`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc]`.

Use `congr 1`. Use extensionality with `i j`. Rewrite using `[Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.of_apply]`. Establish `h1` using `hne i`. Establish `h2` using `habs i`.

Clear the denominators using the available nonvanishing facts.
-/
theorem iwasawa_real : ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), kᵀ * k = 1 ∧ (∀ i, 0 < a i) ∧ (∀ i, n i i = 1) ∧ (∀ i j, j < i → n i j = 0) ∧ g = k * diagonal a * n := by
  intro N g hg
  obtain ⟨k, r, hk, hr, rfl⟩ := exists_orthogonal_mul_upper N g
  have hbt : r.BlockTriangular id := fun i j hij => hr i j hij
  have hdet : r.det ≠ 0 := by
    intro h0
    apply hg
    rw [Matrix.det_mul, h0, mul_zero]
  rw [Matrix.det_of_isUpperTriangular hbt, Finset.prod_ne_zero_iff] at hdet
  have hne : ∀ i, r i i ≠ 0 := fun i => hdet i (Finset.mem_univ i)
  have habs : ∀ i, |r i i| ≠ 0 := fun i => abs_ne_zero.mpr (hne i)
  refine ⟨k * diagonal (fun i => r i i / |r i i|), fun i => |r i i|,
    Matrix.of fun i j => r i j / r i i, ?_, fun i => abs_pos.mpr (hne i), ?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc kᵀ, hk,
      Matrix.one_mul, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [div_mul_div_comm, abs_mul_abs_self, div_self (mul_ne_zero (hne i) (hne i))]
  · intro i
    exact div_self (hne i)
  · intro i j hij
    simp [hr i j hij]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc]
    congr 1
    ext i j
    rw [Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.of_apply]
    have h1 := hne i
    have h2 := habs i
    field_simp

end GlobalTheory.ClassFin
