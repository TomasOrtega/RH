import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct

namespace GlobalTheory.CompanionTheory.AdjointPoly

/- English proof (translation)
Introduce `K _ s n A H₀ a hA ha f`. Establish `hcomm : A * aeval A a = aeval A a * A`. Establish `h : aeval A (X * a) = aeval A (a * X)` using `by rw [mul_comm]`. Simplify `h` using `only [map_mul, aeval_X]`. Establish `hAB : A * aeval A a = 1` using `hcomm.trans ha`.

Establish `hstep : cT s A * H₀ = H₀ * aeval A a`. Combine the equalities or inequalities in the displayed calculation. Establish `cT_mul : ∀ P Q : Matrix (Fin n) (Fin n) K, cT s (P * Q) = cT s Q * cT s P`. Introduce `P Q`. Simplify using `only [cT, Matrix.map_mul, Matrix.transpose_mul]`.

Establish `cT_add : ∀ P Q : Matrix (Fin n) (Fin n) K, cT s (P + Q) = cT s P + cT s Q`. Introduce `P Q`. Use extensionality with `i j`. Simplify using `[cT]`. Establish `cT_C : ∀ c : K, cT s (algebraMap K (Matrix (Fin n) (Fin n) K) c) = algebraMap K (Matrix (Fin n) (Fin n) K) (s c)`.

Introduce `c`. Use extensionality with `i j`. Simplify using `only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Establish `h' : ¬ j = i` using `fun e => h e.symm`. Simplify using `[h, h']`. Proceed by induction on `f using Polynomial.induction_on with`. Consider the case `C c`.

Simplify using `only [aeval_C, Polynomial.map_C, Polynomial.C_comp]`. Rewrite using `[cT_C, Algebra.commutes]`. Consider the case `add p q hp hq`. Simplify using `only [map_add, Polynomial.map_add, Polynomial.add_comp, cT_add, add_mul, mul_add, hp, hq]`. Consider the case `monomial k c ih`.

Establish `e1 : aeval A (C c * X ^ (k + 1)) = A * aeval A (C c * X ^ k)`. Establish `h : aeval A (C c * X ^ (k + 1)) = aeval A (X * (C c * X ^ k))`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, map_mul, aeval_X]`.

Establish `e2 : ((C c * X ^ (k + 1) : K[X]).map s).comp a = ((C c * X ^ k : K[X]).map s).comp a * a`. Simplify using `only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, cT_mul, mul_assoc, hstep, ← mul_assoc, ih, mul_assoc, map_mul (aeval A) (((C c * X ^ k : K[X]).map s).comp a) a]`.
-/
theorem cT_aeval_mul_eq :
    ∀ (K : Type) [Field K] (s : K →+* K) (n : ℕ) (A H₀ : Matrix (Fin n) (Fin n) K) (a : K[X]),
      cT s A * H₀ * A = H₀ → aeval A a * A = 1 →
      ∀ f : K[X], cT s (aeval A f) * H₀ = H₀ * aeval A ((f.map s).comp a) := by
  intro K _ s n A H₀ a hA ha f
  have hcomm : A * aeval A a = aeval A a * A := by
    have h : aeval A (X * a) = aeval A (a * X) := by rw [mul_comm]
    simpa only [map_mul, aeval_X] using h
  have hAB : A * aeval A a = 1 := hcomm.trans ha
  have hstep : cT s A * H₀ = H₀ * aeval A a := by
    calc cT s A * H₀ = cT s A * H₀ * (A * aeval A a) := by rw [hAB, mul_one]
      _ = (cT s A * H₀ * A) * aeval A a := by simp only [mul_assoc]
      _ = H₀ * aeval A a := by rw [hA]
  have cT_mul : ∀ P Q : Matrix (Fin n) (Fin n) K, cT s (P * Q) = cT s Q * cT s P := by
    intro P Q
    simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
  have cT_add : ∀ P Q : Matrix (Fin n) (Fin n) K, cT s (P + Q) = cT s P + cT s Q := by
    intro P Q
    ext i j
    simp [cT]
  have cT_C : ∀ c : K, cT s (algebraMap K (Matrix (Fin n) (Fin n) K) c)
      = algebraMap K (Matrix (Fin n) (Fin n) K) (s c) := by
    intro c
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    by_cases h : i = j
    · subst h; simp
    · have h' : ¬ j = i := fun e => h e.symm
      simp [h, h']
  induction f using Polynomial.induction_on with
  | C c =>
    simp only [aeval_C, Polynomial.map_C, Polynomial.C_comp]
    rw [cT_C, Algebra.commutes]
  | add p q hp hq =>
    simp only [map_add, Polynomial.map_add, Polynomial.add_comp, cT_add, add_mul, mul_add, hp, hq]
  | monomial k c ih =>
    have e1 : aeval A (C c * X ^ (k + 1)) = A * aeval A (C c * X ^ k) := by
      have h : aeval A (C c * X ^ (k + 1)) = aeval A (X * (C c * X ^ k)) := by
        congr 1; ring
      rw [h, map_mul, aeval_X]
    have e2 : ((C c * X ^ (k + 1) : K[X]).map s).comp a
        = ((C c * X ^ k : K[X]).map s).comp a * a := by
      simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp, pow_succ]
      ring
    rw [e1, e2, cT_mul, mul_assoc, hstep, ← mul_assoc, ih, mul_assoc,
      map_mul (aeval A) (((C c * X ^ k : K[X]).map s).comp a) a]

end GlobalTheory.CompanionTheory.AdjointPoly
