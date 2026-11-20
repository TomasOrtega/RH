import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.CoefDiff

open Matrix UpperTheory.V.Weyl

/- English proof (translation)
Introduce `n Ξ Z hZ y`. Use `choose P hP using Ξ.poly`. Set `Q : Fin Ξ.d → Fin Ξ.d → MvPolynomial (Fin n × Fin n) ℂ` to `fun i j => ∑ l, P i l * MvPolynomial.C (Z l j) - ∑ l, MvPolynomial.C (Z i l) * P l j`. Establish `hent : ∀ (g : Matrix (Fin n) (Fin n) ℂ) i j, (Ξ.mat g * Z - Z * Ξ.mat g) i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) (Q i j)`. Introduce `g i j`.

Simplify using `[Q, Matrix.mul_apply, hP, map_sum, mul_comm]`. Rewrite using `[← sub_eq_zero]`. Use extensionality with `i j`. Rewrite using `[hent, Matrix.zero_apply]`. Establish `hQ : Q i j = 0` using `MvPolynomial.eq_of_eval_eq_on_gl (fun g => by`.

Rewrite using `[← hent, hZ (g : Matrix (Fin n) (Fin n) ℂ) g.isUnit, sub_self, Matrix.zero_apply, map_zero])`. Rewrite using `[hQ, map_zero]`.
-/
theorem UpperTheory.V.Weyl.commAll :
    ∀ (n : ℕ) (Ξ : Pre n) (Z : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), (∀ y, IsUnit y → Ξ.mat y * Z = Z * Ξ.mat y) →
      ∀ y, Ξ.mat y * Z = Z * Ξ.mat y := by
  intro n Ξ Z hZ y
  choose P hP using Ξ.poly
  let Q : Fin Ξ.d → Fin Ξ.d → MvPolynomial (Fin n × Fin n) ℂ := fun i j =>
    ∑ l, P i l * MvPolynomial.C (Z l j) - ∑ l, MvPolynomial.C (Z i l) * P l j
  have hent : ∀ (g : Matrix (Fin n) (Fin n) ℂ) i j,
      (Ξ.mat g * Z - Z * Ξ.mat g) i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) (Q i j) := by
    intro g i j
    simp [Q, Matrix.mul_apply, hP, map_sum, mul_comm]
  rw [← sub_eq_zero]
  ext i j
  rw [hent, Matrix.zero_apply]
  have hQ : Q i j = 0 := MvPolynomial.eq_of_eval_eq_on_gl (fun g => by
    rw [← hent, hZ (g : Matrix (Fin n) (Fin n) ℂ) g.isUnit, sub_self, Matrix.zero_apply, map_zero])
  rw [hQ, map_zero]
