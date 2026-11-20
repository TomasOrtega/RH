import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Use extensionality with `a b`. Simplify using `[Formalism.REAL.epow, Matrix.one_apply]`. Consider the case `succ k ih`.

Use extensionality with `a b`. Rewrite using `[pow_succ, ← ih]`. Simplify using `[Formalism.REAL.epow, Matrix.mul_apply]`.
-/
theorem recursive_matrixPower_eq_matrix_pow {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) :
    Matrix.of (Formalism.REAL.epow E k) = (Matrix.of E) ^ k := by
  induction k with
  | zero =>
    ext a b
    simp [Formalism.REAL.epow, Matrix.one_apply]
  | succ k ih =>
    ext a b
    rw [pow_succ, ← ih]
    simp [Formalism.REAL.epow, Matrix.mul_apply]

/- English proof (translation)
Rewrite using `[Finset.sum_comm]`. Simplify using `only [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← Algebra.commutes, ← Algebra.smul_def, ← Algebra.smul_def, smul_smul, mul_comm]`.
-/
theorem scalarMatrix_mul_algebraMatrix_mul_apply {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ((algebraMap ℂ A).mapMatrix P.transpose * M * (algebraMap ℂ A).mapMatrix Q.transpose) a b
      = ∑ c, ∑ d, (P c a * Q b d) • M c d := by
  rw [Finset.sum_comm]
  simp only [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  rw [← Algebra.commutes, ← Algebra.smul_def, ← Algebra.smul_def, smul_smul, mul_comm]

/- English proof (translation)
Establish `hd : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).1 hP`. Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hd`. Establish `h2 : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hd`. Use `set L : Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix P.transpose with hL`. Use `set R : Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix (P⁻¹).transpose with hR`.

Establish `hLR : L * R = 1`. Rewrite using `[hL, hR, ← map_mul, ← Matrix.transpose_mul, h2, Matrix.transpose_one, map_one]`. Establish `hRL : R * L = 1`. Rewrite using `[hL, hR, ← map_mul, ← Matrix.transpose_mul, h1, Matrix.transpose_one, map_one]`. Establish `hE : Matrix.of (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) = L * Matrix.of E * R`.

Use extensionality with `a b`. Rewrite using `[hL, hR, scalarMatrix_mul_algebraMatrix_mul_apply]`. Both sides reduce to the same expression. Establish `hpow : ∀ m : ℕ, (L * Matrix.of E * R) ^ m = L * (Matrix.of E) ^ m * R`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => simp [hLR]`. Consider the case `succ m ih`. Rewrite using `[pow_succ, ih, pow_succ]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hk` using `recursive_matrixPower_eq_matrix_pow (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k`. Rewrite `hk` using `[hE, hpow, ← recursive_matrixPower_eq_matrix_pow]`. Establish `hent : ∀ a, Formalism.REAL.epow (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k a a = ∑ c, ∑ d, (P c a * P⁻¹ a d) • Formalism.REAL.epow E k c d`. Introduce `a`. Use `congrFun (congrFun hk a) a` as an intermediate fact.

Rewrite `this` using `[hL, hR, scalarMatrix_mul_algebraMatrix_mul_apply]`. Conclude with `this`. Unfold `Formalism.REAL.etr`. Simplify using `only [hent]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul, ← Matrix.mul_apply, h1, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem etr_conj_scalar_matrix {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (k : ℕ) :
    Formalism.REAL.etr (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k = Formalism.REAL.etr E k := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  set L : Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix P.transpose with hL
  set R : Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix (P⁻¹).transpose with hR
  have hLR : L * R = 1 := by
    rw [hL, hR, ← map_mul, ← Matrix.transpose_mul, h2, Matrix.transpose_one, map_one]
  have hRL : R * L = 1 := by
    rw [hL, hR, ← map_mul, ← Matrix.transpose_mul, h1, Matrix.transpose_one, map_one]
  have hE : Matrix.of (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) = L * Matrix.of E * R := by
    ext a b
    rw [hL, hR, scalarMatrix_mul_algebraMatrix_mul_apply]
    rfl
  have hpow : ∀ m : ℕ, (L * Matrix.of E * R) ^ m = L * (Matrix.of E) ^ m * R := by
    intro m
    induction m with
    | zero => simp [hLR]
    | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      calc L * Matrix.of E ^ m * R * (L * Matrix.of E * R)
          = L * Matrix.of E ^ m * (R * L) * Matrix.of E * R := by simp only [mul_assoc]
        _ = L * (Matrix.of E ^ m * Matrix.of E) * R := by rw [hRL]; simp only [mul_assoc, one_mul]
  have hk := recursive_matrixPower_eq_matrix_pow (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k
  rw [hE, hpow, ← recursive_matrixPower_eq_matrix_pow] at hk
  have hent : ∀ a, Formalism.REAL.epow (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k a a
      = ∑ c, ∑ d, (P c a * P⁻¹ a d) • Formalism.REAL.epow E k c d := by
    intro a
    have := congrFun (congrFun hk a) a
    rw [hL, hR, scalarMatrix_mul_algebraMatrix_mul_apply] at this
    exact this
  unfold Formalism.REAL.etr
  simp only [hent]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, ← Matrix.mul_apply, h1, Matrix.one_apply, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory
