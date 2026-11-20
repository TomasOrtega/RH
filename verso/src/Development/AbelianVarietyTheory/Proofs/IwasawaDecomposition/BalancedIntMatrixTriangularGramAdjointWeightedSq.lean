import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

/- English proof (translation)
Introduce `n A A' d u v hd hvu huv h`. Use `set a := A.map (Int.cast : ℤ → ℝ) with ha`. Use `set a' := A'.map (Int.cast : ℤ → ℝ) with ha'`. Establish `key : (u * a * v)ᵀ * diagonal d = diagonal d * (u * a' * v)`. Establish `h2` using `congrArg (fun M => vᵀ * M * v) h`.

Simplify using `only [gram] at h2`. Establish `e1 : vᵀ * (aᵀ * (uᵀ * diagonal d * u)) * v = (u * a * v)ᵀ * diagonal d * (u * v)`. Simplify using `only [transpose_mul, Matrix.mul_assoc]`. Establish `e2 : vᵀ * (uᵀ * diagonal d * u * a') * v = (u * v)ᵀ * diagonal d * (u * a' * v)`. Simplify using `only [transpose_mul, Matrix.mul_assoc]`.

Rewrite `h2` using `[e1, e2, huv]`. Simplify using `using h2`. Establish `c1 : ∀ p q, d p * (u * a * v) p q = d q * (u * a' * v) q p`. Introduce `p q`. Use `congrFun (congrFun key q) p` as an intermediate fact.

Simplify using `only [mul_diagonal, diagonal_mul, transpose_apply] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `htr : ∑ p, ∑ q, (u * a' * v) q p * (u * a * v) p q = (((A' * A).trace : ℤ) : ℝ)`. Establish `e : ∑ p, ∑ q, (u * a' * v) q p * (u * a * v) p q = ((u * a' * v) * (u * a * v)).trace`. Rewrite using `[Finset.sum_comm]`.

Simplify using `[Matrix.trace, Matrix.mul_apply]`. Rewrite using `[e]`. Establish `: (u * a' * v) * (u * a * v) = u * (a' * a) * v`. Rewrite using `[show (u * a' * v) * (u * a * v) = u * a' * (v * u) * a * v by simp only [Matrix.mul_assoc], hvu]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`.

Rewrite using `[this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hvu, Matrix.one_mul]`. Rewrite using `[ha, ha']`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply]`. Use `push_cast`. Both sides reduce to the same expression.

Use `⟨c1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← htr]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Establish `hq` using `(hd q).ne'`. Rewrite using `[div_mul_eq_mul_div, div_eq_iff hq, sq, ← mul_assoc, c1 p q]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← htr, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Establish `hp` using `(hd p).ne'`. Rewrite using `[div_mul_eq_mul_div, div_eq_iff hp, sq, ← mul_assoc, ← c1 p q]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem adjoint_weighted_sq_trace : ∀ (n : ℕ) (A A' : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ) (u v : Matrix (Fin n) (Fin n) ℝ), (∀ i, 0 < d i) → v * u = 1 → u * v = 1 → (A.map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * A'.map (Int.cast : ℤ → ℝ) → (∀ p q, d p * (u * A.map (Int.cast : ℤ → ℝ) * v) p q = d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) q p) ∧ (∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 = (((A' * A).trace : ℤ) : ℝ)) ∧ ∑ p, ∑ q, d p / d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 = (((A' * A).trace : ℤ) : ℝ) := by
  intro n A A' d u v hd hvu huv h
  set a := A.map (Int.cast : ℤ → ℝ) with ha
  set a' := A'.map (Int.cast : ℤ → ℝ) with ha'
  have key : (u * a * v)ᵀ * diagonal d = diagonal d * (u * a' * v) := by
    have h2 := congrArg (fun M => vᵀ * M * v) h
    simp only [gram] at h2
    have e1 : vᵀ * (aᵀ * (uᵀ * diagonal d * u)) * v = (u * a * v)ᵀ * diagonal d * (u * v) := by
      simp only [transpose_mul, Matrix.mul_assoc]
    have e2 : vᵀ * (uᵀ * diagonal d * u * a') * v = (u * v)ᵀ * diagonal d * (u * a' * v) := by
      simp only [transpose_mul, Matrix.mul_assoc]
    rw [e1, e2, huv] at h2
    simpa using h2
  have c1 : ∀ p q, d p * (u * a * v) p q = d q * (u * a' * v) q p := by
    intro p q
    have := congrFun (congrFun key q) p
    simp only [mul_diagonal, diagonal_mul, transpose_apply] at this
    linarith
  have htr : ∑ p, ∑ q, (u * a' * v) q p * (u * a * v) p q = (((A' * A).trace : ℤ) : ℝ) := by
    have e : ∑ p, ∑ q, (u * a' * v) q p * (u * a * v) p q = ((u * a' * v) * (u * a * v)).trace := by
      rw [Finset.sum_comm]; simp [Matrix.trace, Matrix.mul_apply]
    rw [e]
    have : (u * a' * v) * (u * a * v) = u * (a' * a) * v := by
      rw [show (u * a' * v) * (u * a * v) = u * a' * (v * u) * a * v by simp only [Matrix.mul_assoc], hvu]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hvu, Matrix.one_mul]
    rw [ha, ha']
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply]
    push_cast; rfl
  refine ⟨c1, ?_, ?_⟩
  · rw [← htr]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have hq := (hd q).ne'
    rw [div_mul_eq_mul_div, div_eq_iff hq, sq, ← mul_assoc, c1 p q]; ring
  · rw [← htr, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have hp := (hd p).ne'
    rw [div_mul_eq_mul_div, div_eq_iff hp, sq, ← mul_assoc, ← c1 p q]; ring

end GlobalTheory.RedTh
