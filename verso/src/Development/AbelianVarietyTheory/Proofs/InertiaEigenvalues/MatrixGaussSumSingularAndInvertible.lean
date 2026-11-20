import Mathlib

open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft g) (fun x : GL (Fin r) k => ((ξ (Matrix.GeneralLinearGroup.det g) : Rˣ) : R) * ((((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (a * (x : Matrix (Fin r) (Fin r) k)))))]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Establish `h2 : ξ (Matrix.GeneralLinearGroup.det (g * x)) = ξ (Matrix.GeneralLinearGroup.det g) * ξ (Matrix.GeneralLinearGroup.det x)`. Rewrite using `[map_mul, map_mul]`. Establish `h3 : ((ξ (Matrix.GeneralLinearGroup.det g) : Rˣ) : R) * (((ξ (Matrix.GeneralLinearGroup.det (g * x)))⁻¹ : Rˣ) : R) = (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R)`.

Rewrite using `[h2, ← Units.val_mul, mul_inv, mul_inv_cancel_left]`. Establish `h4 : ((g * x : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = (g : Matrix (Fin r) (Fin r) k) * (x : Matrix (Fin r) (Fin r) k)` using `rfl`. Rewrite using `[Equiv.coe_mulLeft, ← mul_assoc, h3, h4, Matrix.mul_assoc]`.
-/
theorem matrixGaussSum_mul_unit (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type)
    [CommRing R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ) (a : Matrix (Fin r) (Fin r) k)
    (g : GL (Fin r) k) :
    (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) *
      ψ (Matrix.trace ((a * (g : Matrix (Fin r) (Fin r) k)) * (x : Matrix (Fin r) (Fin r) k)))) =
    ((ξ (Matrix.GeneralLinearGroup.det g) : Rˣ) : R) *
      (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) *
        ψ (Matrix.trace (a * (x : Matrix (Fin r) (Fin r) k)))) := by
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft g)
    (fun x : GL (Fin r) k => ((ξ (Matrix.GeneralLinearGroup.det g) : Rˣ) : R) *
      ((((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) *
        ψ (Matrix.trace (a * (x : Matrix (Fin r) (Fin r) k)))))]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h2 : ξ (Matrix.GeneralLinearGroup.det (g * x)) =
      ξ (Matrix.GeneralLinearGroup.det g) * ξ (Matrix.GeneralLinearGroup.det x) := by
    rw [map_mul, map_mul]
  have h3 : ((ξ (Matrix.GeneralLinearGroup.det g) : Rˣ) : R) *
      (((ξ (Matrix.GeneralLinearGroup.det (g * x)))⁻¹ : Rˣ) : R) =
      (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) := by
    rw [h2, ← Units.val_mul, mul_inv, mul_inv_cancel_left]
  have h4 : ((g * x : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) =
      (g : Matrix (Fin r) (Fin r) k) * (x : Matrix (Fin r) (Fin r) k) := rfl
  rw [Equiv.coe_mulLeft, ← mul_assoc, h3, h4, Matrix.mul_assoc]

/- English proof (translation)
Take `⟨v, hv, hav⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr ha`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hv`. Establish `hi' : v i ≠ 0` using `hi`. Set `w : Fin r → k` to `Pi.single i (((t : k) - 1) / v i)`. Establish `hdet : (1 + Matrix.vecMulVec v w).det = (t : k)`.

Rewrite using `[Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]`. Simplify using `only [w, single_dotProduct]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + Matrix.vecMulVec v w) (by rw [hdet]; exact t.ne_zero), ?_, ?_⟩` and prove the remaining obligations.

Use `ext`. Conclude with `hdet`. Express the relevant statement in the definitionally equal form `a * (1 + Matrix.vecMulVec v w) = a`. Rewrite using `[Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, hav]`. Simplify using the standard rewrite rules.
-/
theorem exists_gl_det_eq_mul_eq_of_det_eq_zero (k : Type) [Field k] (r : ℕ)
    (a : Matrix (Fin r) (Fin r) k) (ha : a.det = 0) (t : kˣ) :
    ∃ g : GL (Fin r) k, Matrix.GeneralLinearGroup.det g = t ∧
      a * (g : Matrix (Fin r) (Fin r) k) = a := by
  obtain ⟨v, hv, hav⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr ha
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hi' : v i ≠ 0 := hi
  let w : Fin r → k := Pi.single i (((t : k) - 1) / v i)
  have hdet : (1 + Matrix.vecMulVec v w).det = (t : k) := by
    rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp only [w, single_dotProduct]
    field_simp
    ring
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + Matrix.vecMulVec v w)
    (by rw [hdet]; exact t.ne_zero), ?_, ?_⟩
  · ext
    exact hdet
  · change a * (1 + Matrix.vecMulVec v w) = a
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, hav]
    simp

/- English proof (translation)
Introduce `k _ _ _ R _ _ ψ ξ r _ hξ`. Use `⟨fun a ha => ?_, fun a => ?_⟩` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, ξ t ≠ 1 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hξ (MonoidHom.ext h)`. Take `⟨g, hg, hag⟩` from `exists_gl_det_eq_mul_eq_of_det_eq_zero k r a ha t`. Establish `h` using `matrixGaussSum_mul_unit k R ψ ξ r a g`. Rewrite `h` using `[hag, hg]`. Establish `h1 : ((ξ t : Rˣ) : R) ≠ 1` using `fun h' => ht (Units.ext h')`.

Assume the negation of the conclusion as `hS`. Conclude with `h1 (mul_right_cancel₀ hS (h.symm.trans (one_mul _).symm))`. Establish `h` using `matrixGaussSum_mul_unit k R ψ ξ r 1 a`. Rewrite `h` using `[Matrix.one_mul]`. Then use the resulting hypothesis.
-/
theorem matrixGaussSum_singular_and_invertible :
    ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type) [CommRing R] [IsDomain R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → (∀ a : Matrix (Fin r) (Fin r) k, a.det = 0 → (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (a * (x : Matrix (Fin r) (Fin r) k)))) = 0) ∧ ∀ a : GL (Fin r) k, (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace ((a : Matrix (Fin r) (Fin r) k) * (x : Matrix (Fin r) (Fin r) k)))) = ((ξ (Matrix.GeneralLinearGroup.det a) : Rˣ) : R) * (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) := by
  intro k _ _ _ R _ _ ψ ξ r _ hξ
  refine ⟨fun a ha => ?_, fun a => ?_⟩
  · obtain ⟨t, ht⟩ : ∃ t, ξ t ≠ 1 := by
      by_contra h
      push_neg at h
      exact hξ (MonoidHom.ext h)
    obtain ⟨g, hg, hag⟩ := exists_gl_det_eq_mul_eq_of_det_eq_zero k r a ha t
    have h := matrixGaussSum_mul_unit k R ψ ξ r a g
    rw [hag, hg] at h
    have h1 : ((ξ t : Rˣ) : R) ≠ 1 := fun h' => ht (Units.ext h')
    by_contra hS
    exact h1 (mul_right_cancel₀ hS (h.symm.trans (one_mul _).symm))
  · have h := matrixGaussSum_mul_unit k R ψ ξ r 1 a
    rwa [Matrix.one_mul] at h

end GlobalTheory
