import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.NormEDS

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

/- English proof (translation)
The claim follows from `sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hM)`.
-/
private theorem eq_of_mul_sub_eq_zero {R : Type*} [CommRing R] [IsDomain R] {M x y : R}
    (hM : M ≠ 0) (h : M * (x - y) = 0) : x = y :=
  sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hM)

section Sequence

variable {R : Type*} [CommRing R] [IsDomain R]

/- English proof (translation)
Establish `nat : ∀ k : ℕ, normEDS b 0 d k = 0 ↔ (3 : ℤ) ∣ k`. Introduce `k`. Proceed by induction on `k using normEDSRec' with`. Consider the case `zero => simp [normEDS_zero]`. Consider the case `one => simp only [Nat.cast_one, normEDS_one, one_ne_zero, false_iff]`.

Use linear arithmetic over natural numbers and integers. Consider the case `two => simp only [Nat.cast_ofNat, normEDS_two, hb, false_iff]`. Use linear arithmetic over natural numbers and integers. Consider the case `three => simp [normEDS_three]`. Consider the case `four`.

Simplify using `only [Nat.cast_ofNat, normEDS_four, mul_eq_zero, hb, hd, or_self, false_iff]`. Use linear arithmetic over natural numbers and integers. Consider the case `even m ih`. Establish `key` using `normEDS_even b 0 d ((m : ℤ) + 3)`. Establish `z1` using `ih (m + 1) (by omega)`.

Establish `z2` using `ih (m + 2) (by omega)`. Establish `z3` using `ih (m + 3) (by omega)`. Establish `z4` using `ih (m + 4) (by omega)`. Establish `z5` using `ih (m + 5) (by omega)`. Move the coercions through the operations in `at z1 z2 z3 z4 z5 ⊢`.

Rewrite `key` using `[show (m : ℤ) + 3 - 1 = m + 2 by ring, show (m : ℤ) + 3 + 2 = m + 5 by ring, show (m : ℤ) + 3 - 2 = m + 1 by ring, show (m : ℤ) + 3 + 1 = m + 4 by ring]`. Break down `(by omega : (m : ℤ) % 3 = 0 ∨ (m : ℤ) % 3 = 1 ∨ (m : ℤ) % 3 = 2) with hm | hm | hm` into its components or cases. Establish `e3 : normEDS b 0 d ((m : ℤ) + 3) = 0` using `z3.mpr (by omega)`. Rewrite `key` using `[e3]`. Simplify using `only [mul_zero, zero_mul, sub_zero, mul_eq_zero, hb, or_false] at key`.

Simplify using `only [key, true_iff]`. Use linear arithmetic over natural numbers and integers. Establish `e5 : normEDS b 0 d ((m : ℤ) + 5) = 0` using `z5.mpr (by omega)`. Establish `n1 : normEDS b 0 d ((m : ℤ) + 1) ≠ 0` using `fun h => by have := z1.mp h; omega`. Establish `n3 : normEDS b 0 d ((m : ℤ) + 3) ≠ 0` using `fun h => by have := z3.mp h; omega`.

Establish `n4 : normEDS b 0 d ((m : ℤ) + 4) ≠ 0` using `fun h => by have := z4.mp h; omega`. Rewrite `key` using `[e5, mul_zero, zero_sub]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite `key` using `[h, zero_mul]`.

Conclude with `absurd key.symm (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero n1 n3) (pow_ne_zero _ n4)))`. Introduce `h`. Use linear arithmetic over natural numbers and integers. Establish `e1 : normEDS b 0 d ((m : ℤ) + 1) = 0` using `z1.mpr (by omega)`. Establish `n2 : normEDS b 0 d ((m : ℤ) + 2) ≠ 0` using `fun h => by have := z2.mp h; omega`.

Establish `n3 : normEDS b 0 d ((m : ℤ) + 3) ≠ 0` using `fun h => by have := z3.mp h; omega`. Establish `n5 : normEDS b 0 d ((m : ℤ) + 5) ≠ 0` using `fun h => by have := z5.mp h; omega`. Rewrite `key` using `[e1, zero_mul, zero_mul, sub_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite `key` using `[h, zero_mul]`. Conclude with `absurd key.symm (mul_ne_zero (mul_ne_zero (pow_ne_zero _ n2) n3) n5)`. Introduce `h`. Use linear arithmetic over natural numbers and integers. Consider the case `odd m ih`.

Establish `key` using `normEDS_odd b 0 d ((m : ℤ) + 2)`. Establish `z1` using `ih (m + 1) (by omega)`. Establish `z2` using `ih (m + 2) (by omega)`. Establish `z3` using `ih (m + 3) (by omega)`. Establish `z4` using `ih (m + 4) (by omega)`.

Move the coercions through the operations in `at z1 z2 z3 z4 ⊢`. Rewrite `key` using `[show (m : ℤ) + 2 + 2 = m + 4 by ring, show (m : ℤ) + 2 - 1 = m + 1 by ring, show (m : ℤ) + 2 + 1 = m + 3 by ring]`. Rewrite using `[key]`. Break down `(by omega : (m : ℤ) % 3 = 0 ∨ (m : ℤ) % 3 = 1 ∨ (m : ℤ) % 3 = 2) with hm | hm | hm` into its components or cases. Establish `e3 : normEDS b 0 d ((m : ℤ) + 3) = 0` using `z3.mpr (by omega)`.

Establish `n2 : normEDS b 0 d ((m : ℤ) + 2) ≠ 0` using `fun h => by have := z2.mp h; omega`. Establish `n4 : normEDS b 0 d ((m : ℤ) + 4) ≠ 0` using `fun h => by have := z4.mp h; omega`. Rewrite using `[e3]`. Simplify using `only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero, mul_eq_zero, n4, pow_eq_zero_iff, n2, or_self, false_iff]`. Use linear arithmetic over natural numbers and integers.

Establish `e2 : normEDS b 0 d ((m : ℤ) + 2) = 0` using `z2.mpr (by omega)`. Establish `n1 : normEDS b 0 d ((m : ℤ) + 1) ≠ 0` using `fun h => by have := z1.mp h; omega`. Establish `n3 : normEDS b 0 d ((m : ℤ) + 3) ≠ 0` using `fun h => by have := z3.mp h; omega`. Rewrite using `[e2]`. Simplify using `only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_sub, neg_eq_zero, mul_eq_zero, n1, pow_eq_zero_iff, n3, or_self, false_iff]`.

Use linear arithmetic over natural numbers and integers. Establish `e1 : normEDS b 0 d ((m : ℤ) + 1) = 0` using `z1.mpr (by omega)`. Establish `e4 : normEDS b 0 d ((m : ℤ) + 4) = 0` using `z4.mpr (by omega)`. Rewrite using `[e1, e4]`. Simplify using `only [zero_mul, sub_self, true_iff]`.

Use linear arithmetic over natural numbers and integers. Break down `Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩` into its components or cases. Conclude with `nat k`. Rewrite using `[normEDS_neg, neg_eq_zero, nat k, dvd_neg]`.
-/
theorem normEDS_eq_zero_iff_of_three {b d : R} (hb : b ≠ 0) (hd : d ≠ 0) (n : ℤ) :
    normEDS b 0 d n = 0 ↔ (3 : ℤ) ∣ n := by
  have nat : ∀ k : ℕ, normEDS b 0 d k = 0 ↔ (3 : ℤ) ∣ k := by
    intro k
    induction k using normEDSRec' with
    | zero => simp [normEDS_zero]
    | one => simp only [Nat.cast_one, normEDS_one, one_ne_zero, false_iff]; omega
    | two => simp only [Nat.cast_ofNat, normEDS_two, hb, false_iff]; omega
    | three => simp [normEDS_three]
    | four =>
      simp only [Nat.cast_ofNat, normEDS_four, mul_eq_zero, hb, hd, or_self, false_iff]; omega
    | even m ih =>
      have key := normEDS_even b 0 d ((m : ℤ) + 3)
      have z1 := ih (m + 1) (by omega)
      have z2 := ih (m + 2) (by omega)
      have z3 := ih (m + 3) (by omega)
      have z4 := ih (m + 4) (by omega)
      have z5 := ih (m + 5) (by omega)
      push_cast at z1 z2 z3 z4 z5 ⊢
      rw [show (m : ℤ) + 3 - 1 = m + 2 by ring, show (m : ℤ) + 3 + 2 = m + 5 by ring,
        show (m : ℤ) + 3 - 2 = m + 1 by ring, show (m : ℤ) + 3 + 1 = m + 4 by ring] at key
      rcases (by omega : (m : ℤ) % 3 = 0 ∨ (m : ℤ) % 3 = 1 ∨ (m : ℤ) % 3 = 2) with hm | hm | hm
      · have e3 : normEDS b 0 d ((m : ℤ) + 3) = 0 := z3.mpr (by omega)
        rw [e3] at key
        simp only [mul_zero, zero_mul, sub_zero, mul_eq_zero, hb, or_false] at key
        simp only [key, true_iff]; omega
      · have e5 : normEDS b 0 d ((m : ℤ) + 5) = 0 := z5.mpr (by omega)
        have n1 : normEDS b 0 d ((m : ℤ) + 1) ≠ 0 := fun h => by have := z1.mp h; omega
        have n3 : normEDS b 0 d ((m : ℤ) + 3) ≠ 0 := fun h => by have := z3.mp h; omega
        have n4 : normEDS b 0 d ((m : ℤ) + 4) ≠ 0 := fun h => by have := z4.mp h; omega
        rw [e5, mul_zero, zero_sub] at key
        constructor
        · intro h
          rw [h, zero_mul] at key
          exact absurd key.symm (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero n1 n3) (pow_ne_zero _ n4)))
        · intro h; omega
      · have e1 : normEDS b 0 d ((m : ℤ) + 1) = 0 := z1.mpr (by omega)
        have n2 : normEDS b 0 d ((m : ℤ) + 2) ≠ 0 := fun h => by have := z2.mp h; omega
        have n3 : normEDS b 0 d ((m : ℤ) + 3) ≠ 0 := fun h => by have := z3.mp h; omega
        have n5 : normEDS b 0 d ((m : ℤ) + 5) ≠ 0 := fun h => by have := z5.mp h; omega
        rw [e1, zero_mul, zero_mul, sub_zero] at key
        constructor
        · intro h
          rw [h, zero_mul] at key
          exact absurd key.symm (mul_ne_zero (mul_ne_zero (pow_ne_zero _ n2) n3) n5)
        · intro h; omega
    | odd m ih =>
      have key := normEDS_odd b 0 d ((m : ℤ) + 2)
      have z1 := ih (m + 1) (by omega)
      have z2 := ih (m + 2) (by omega)
      have z3 := ih (m + 3) (by omega)
      have z4 := ih (m + 4) (by omega)
      push_cast at z1 z2 z3 z4 ⊢
      rw [show (m : ℤ) + 2 + 2 = m + 4 by ring, show (m : ℤ) + 2 - 1 = m + 1 by ring,
        show (m : ℤ) + 2 + 1 = m + 3 by ring] at key
      rw [key]
      rcases (by omega : (m : ℤ) % 3 = 0 ∨ (m : ℤ) % 3 = 1 ∨ (m : ℤ) % 3 = 2) with hm | hm | hm
      · have e3 : normEDS b 0 d ((m : ℤ) + 3) = 0 := z3.mpr (by omega)
        have n2 : normEDS b 0 d ((m : ℤ) + 2) ≠ 0 := fun h => by have := z2.mp h; omega
        have n4 : normEDS b 0 d ((m : ℤ) + 4) ≠ 0 := fun h => by have := z4.mp h; omega
        rw [e3]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero,
          mul_eq_zero, n4, pow_eq_zero_iff, n2, or_self, false_iff]
        omega
      · have e2 : normEDS b 0 d ((m : ℤ) + 2) = 0 := z2.mpr (by omega)
        have n1 : normEDS b 0 d ((m : ℤ) + 1) ≠ 0 := fun h => by have := z1.mp h; omega
        have n3 : normEDS b 0 d ((m : ℤ) + 3) ≠ 0 := fun h => by have := z3.mp h; omega
        rw [e2]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_sub,
          neg_eq_zero, mul_eq_zero, n1, pow_eq_zero_iff, n3, or_self, false_iff]
        omega
      · have e1 : normEDS b 0 d ((m : ℤ) + 1) = 0 := z1.mpr (by omega)
        have e4 : normEDS b 0 d ((m : ℤ) + 4) = 0 := z4.mpr (by omega)
        rw [e1, e4]
        simp only [zero_mul, sub_self, true_iff]
        omega
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · exact nat k
  · rw [normEDS_neg, neg_eq_zero, nat k, dvd_neg]

omit [IsDomain R] in

/- English proof (translation)
Simplify using `[normEDS, hn]`.
-/
theorem normEDS_zero_left_of_even (c d : R) {n : ℤ} (hn : Even n) : normEDS 0 c d n = 0 := by
  simp [normEDS, hn]

end Sequence

section Values

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

noncomputable def psiAt (x y : R) (n : ℤ) : R :=
  (W.ψ n).evalEval x y

/- English proof (translation)
Rewrite using `[psiAt, WeierstrassCurve.ψ, ← coe_evalEvalRingHom, map_normEDS]`. Simplify using `only [coe_evalEvalRingHom, ψ₂, evalEval_polynomialY, evalEval_C]`.
-/
theorem psiAt_eq (x y : R) (n : ℤ) :
    psiAt W x y n =
      normEDS (2 * y + W.a₁ * x + W.a₃) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n := by
  rw [psiAt, WeierstrassCurve.ψ, ← coe_evalEvalRingHom, map_normEDS]
  simp only [coe_evalEvalRingHom, ψ₂, evalEval_polynomialY, evalEval_C]

/- English proof (translation)
Simplify using `only [psiAt_eq]`. Conclude with `normEDS_somos ..`.
-/
theorem psiAt_somos (x y : R) (n : ℤ) :
    psiAt W x y (n + 2) * psiAt W x y (n - 2) =
      (2 * y + W.a₁ * x + W.a₃) ^ 2 * psiAt W x y (n + 1) * psiAt W x y (n - 1) -
        W.Ψ₃.eval x * psiAt W x y n ^ 2 := by
  simp only [psiAt_eq]
  exact normEDS_somos ..

/- English proof (translation)
Simplify using `only [psiAt_eq]`. Conclude with `normEDS_invariant ..`.
-/
theorem psiAt_invariant (x y : R) (n : ℤ) :
    W.Ψ₃.eval x * (psiAt W x y (n + 2) * psiAt W x y (n - 1) ^ 2 +
        psiAt W x y (n - 2) * psiAt W x y (n + 1) ^ 2) =
      ((2 * y + W.a₁ * x + W.a₃) ^ 4 + W.preΨ₄.eval x) * psiAt W x y (n - 1) *
          psiAt W x y n * psiAt W x y (n + 1) -
        (2 * y + W.a₁ * x + W.a₃) ^ 2 * W.Ψ₃.eval x * psiAt W x y n ^ 3 := by
  simp only [psiAt_eq]
  exact normEDS_invariant ..

/- English proof (translation)
Simplify using `[psiAt_eq, normEDS_zero]`.
-/
theorem psiAt_zero (x y : R) : psiAt W x y 0 = 0 := by simp [psiAt_eq, normEDS_zero]
/- English proof (translation)
Simplify using `[psiAt_eq, normEDS_one]`.
-/
theorem psiAt_one (x y : R) : psiAt W x y 1 = 1 := by simp [psiAt_eq, normEDS_one]
/- English proof (translation)
Simplify using `[psiAt_eq, normEDS_two]`.
-/
theorem psiAt_two (x y : R) : psiAt W x y 2 = 2 * y + W.a₁ * x + W.a₃ := by
  simp [psiAt_eq, normEDS_two]
/- English proof (translation)
Simplify using `[psiAt_eq, normEDS_three]`.
-/
theorem psiAt_three (x y : R) : psiAt W x y 3 = W.Ψ₃.eval x := by simp [psiAt_eq, normEDS_three]
/- English proof (translation)
Simplify using `[psiAt_eq, normEDS_neg]`.
-/
theorem psiAt_neg (x y : R) (n : ℤ) : psiAt W x y (-n) = -psiAt W x y n := by
  simp [psiAt_eq, normEDS_neg]

/- English proof (translation)
The claim follows from `AdjoinRoot.evalEval_mk h g`.
-/
private theorem evalEval_mkW {x y : R} (h : W.toAffine.Equation x y) (g : R[X][Y]) :
    AdjoinRoot.evalEval (p := W.toAffine.polynomial) h (Affine.CoordinateRing.mk W g) =
      g.evalEval x y :=
  AdjoinRoot.evalEval_mk h g

/- English proof (translation)
Use `congrArg (AdjoinRoot.evalEval (p := W.toAffine.polynomial) h) (Affine.CoordinateRing.mk_Ψ_sq W n)` as an intermediate fact. Rewrite `this` using `[← Affine.CoordinateRing.mk_ψ, map_pow, evalEval_mkW W h, evalEval_mkW W h, evalEval_C]`. Conclude with `this`.
-/
theorem psiAt_sq {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) :
    psiAt W x y n ^ 2 = (W.ΨSq n).eval x := by
  have := congrArg (AdjoinRoot.evalEval (p := W.toAffine.polynomial) h)
    (Affine.CoordinateRing.mk_Ψ_sq W n)
  rw [← Affine.CoordinateRing.mk_ψ, map_pow, evalEval_mkW W h, evalEval_mkW W h, evalEval_C] at this
  exact this

/- English proof (translation)
Use `congrArg (AdjoinRoot.evalEval (p := W.toAffine.polynomial) h) (Affine.CoordinateRing.mk_φ W n)` as an intermediate fact. Rewrite `this` using `[evalEval_mkW W h, evalEval_mkW W h, evalEval_C, WeierstrassCurve.φ]`. Rewrite using `[← this, psiAt, psiAt, psiAt]`. Simplify using `only [evalEval_sub, evalEval_mul, evalEval_pow, evalEval_C, eval_X]`.
-/
theorem Phi_eval {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.Φ n).eval x = x * psiAt W x y n ^ 2 - psiAt W x y (n + 1) * psiAt W x y (n - 1) := by
  have := congrArg (AdjoinRoot.evalEval (p := W.toAffine.polynomial) h)
    (Affine.CoordinateRing.mk_φ W n)
  rw [evalEval_mkW W h, evalEval_mkW W h, evalEval_C, WeierstrassCurve.φ] at this
  rw [← this, psiAt, psiAt, psiAt]
  simp only [evalEval_sub, evalEval_mul, evalEval_pow, evalEval_C, eval_X]

/- English proof (translation)
Rewrite `h` using `[equation_iff]`. Simplify using `only [b₂, b₄, b₆]`. Take the linear combination `4 * h`.
-/
theorem two_y_sq {x y : R} (h : W.toAffine.Equation x y) :
    (2 * y + W.a₁ * x + W.a₃) ^ 2 = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  rw [equation_iff] at h
  simp only [b₂, b₄, b₆]
  linear_combination 4 * h

/- English proof (translation)
Simplify using `[Ψ₃]`.
-/
theorem Psi3_eval (x : R) :
    W.Ψ₃.eval x = 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ := by
  simp [Ψ₃]

/- English proof (translation)
Simplify using `[preΨ₄]`.
-/
theorem prePsi4_eval (x : R) :
    W.preΨ₄.eval x = 2 * x ^ 6 + W.b₂ * x ^ 5 + 5 * W.b₄ * x ^ 4 + 10 * W.b₆ * x ^ 3 +
      10 * W.b₈ * x ^ 2 + (W.b₂ * W.b₈ - W.b₄ * W.b₆) * x + (W.b₄ * W.b₈ - W.b₆ ^ 2) := by
  simp [preΨ₄]

/- English proof (translation)
Rewrite `h` using `[equation_iff]`. Rewrite using `[Psi3_eval]`. Simplify using `only [b₂, b₄, b₆, b₈]`. Take the linear combination `(-(W.a₁ ^ 2 + 4 * W.a₂) - 12 * x) * h + ((-W.a₁ * W.a₄ + W.a₂ * W.a₃) + (W.a₁ ^ 2 + 2 * W.a₂) * y + (-W.a₁ * W.a₂ + 3 * W.a₃) * x + 6 * x * y) * hy`.
-/
theorem Psi3_eval_of_two_y {x y : R} (h : W.toAffine.Equation x y)
    (hy : 2 * y + W.a₁ * x + W.a₃ = 0) :
    W.Ψ₃.eval x = -(W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) ^ 2 := by
  rw [equation_iff] at h
  rw [Psi3_eval]
  simp only [b₂, b₄, b₆, b₈]
  linear_combination (-(W.a₁ ^ 2 + 4 * W.a₂) - 12 * x) * h +
    ((-W.a₁ * W.a₄ + W.a₂ * W.a₃) + (W.a₁ ^ 2 + 2 * W.a₂) * y + (-W.a₁ * W.a₂ + 3 * W.a₃) * x +
      6 * x * y) * hy

/- English proof (translation)
Rewrite using `[show (2 * y + W.a₁ * x + W.a₃) ^ 4 = ((2 * y + W.a₁ * x + W.a₃) ^ 2) ^ 2 by ring, two_y_sq W h, prePsi4_eval, Psi3_eval]`. Take the linear combination `x ^ 2 * W.b_relation`.
-/
theorem two_y_pow_four_add {x y : R} (h : W.toAffine.Equation x y) :
    (2 * y + W.a₁ * x + W.a₃) ^ 4 + W.preΨ₄.eval x =
      (6 * x ^ 2 + W.b₂ * x + W.b₄) * W.Ψ₃.eval x := by
  rw [show (2 * y + W.a₁ * x + W.a₃) ^ 4 = ((2 * y + W.a₁ * x + W.a₃) ^ 2) ^ 2 by ring,
    two_y_sq W h, prePsi4_eval, Psi3_eval]
  linear_combination x ^ 2 * W.b_relation

end Values

section Algebra

variable {F : Type*} [Field F]

/- English proof (translation)
Use `eq_of_mul_sub_eq_zero (M := c0 * w0 ^ 4 * wm1 ^ 4 * (x0 - xn) ^ 2) ?_ ?_` and prove the remaining obligations. Establish `: x0 - xn ≠ 0` using `by rwa [← neg_sub, neg_ne_zero]`. Simplify using `[hc0, hw0, hwm1, this]`. Take the linear combination `(-b2*w0^4*w1^2*wm1^4*x0^3 + b2*w0^2*w1^3*wm1^5*x0^2 - 3*b4*w0^4*w1^2*wm1^4*x0^2 + 2*b4*w0^2*w1^3*wm1^5*x0 - 3*b6*w0^4*w1^2*wm1^4*x0 + b6*w0^2*w1^3*wm1^5 - b8*w0^4*w1^2*wm1^4 + be^2*w0^2*w1^3*wm1^5 - 3*w0^4*w1^2*wm1^4*x0^4 + 4*w0^2*w1^3*wm1^5*x0^3) * hbe + (b2*w0^4*w1^2*wm1^4*x0^2 …`.
-/
private theorem step_alg {b2 b4 b6 b8 x0 be c0 d0 wm2 wm1 w0 w1 w2 xm1 xn X : F}
    (hb8 : 4 * b8 = b2 * b6 - b4 ^ 2)
    (hbe : be ^ 2 = 4 * x0 ^ 3 + b2 * x0 ^ 2 + 2 * b4 * x0 + b6)
    (hc : c0 = 3 * x0 ^ 4 + b2 * x0 ^ 3 + 3 * b4 * x0 ^ 2 + 3 * b6 * x0 + b8)
    (hd : d0 = 2 * x0 ^ 6 + b2 * x0 ^ 5 + 5 * b4 * x0 ^ 4 + 10 * b6 * x0 ^ 3 + 10 * b8 * x0 ^ 2 +
      (b2 * b8 - b4 * b6) * x0 + (b4 * b8 - b6 ^ 2))
    (hinv : c0 * (w2 * wm1 ^ 2 + wm2 * w1 ^ 2) =
      (be ^ 4 + d0) * wm1 * w0 * w1 - be ^ 2 * c0 * w0 ^ 3)
    (hxm : xm1 * wm1 ^ 2 = x0 * wm1 ^ 2 - w0 * wm2)
    (hxn : xn * w0 ^ 2 = x0 * w0 ^ 2 - w1 * wm1)
    (hS : (X + xm1) * (xn - x0) ^ 2 =
      2 * xn * x0 * (xn + x0) + b2 * xn * x0 + b4 * (xn + x0) + b6)
    (hc0 : c0 ≠ 0) (hw0 : w0 ≠ 0) (hwm1 : wm1 ≠ 0) (hx : xn - x0 ≠ 0) :
    X * w1 ^ 2 = x0 * w1 ^ 2 - w2 * w0 := by
  refine eq_of_mul_sub_eq_zero (M := c0 * w0 ^ 4 * wm1 ^ 4 * (x0 - xn) ^ 2) ?_ ?_
  · have : x0 - xn ≠ 0 := by rwa [← neg_sub, neg_ne_zero]
    simp [hc0, hw0, hwm1, this]
  · linear_combination (-b2*w0^4*w1^2*wm1^4*x0^3 + b2*w0^2*w1^3*wm1^5*x0^2 - 3*b4*w0^4*w1^2*wm1^4*x0^2 + 2*b4*w0^2*w1^3*wm1^5*x0 - 3*b6*w0^4*w1^2*wm1^4*x0 + b6*w0^2*w1^3*wm1^5 - b8*w0^4*w1^2*wm1^4 + be^2*w0^2*w1^3*wm1^5 - 3*w0^4*w1^2*wm1^4*x0^4 + 4*w0^2*w1^3*wm1^5*x0^3) * hbe + (b2*w0^4*w1^2*wm1^4*x0^2 - b2*w0^2*w1^3*wm1^5*x0 + 2*b4*w0^4*w1^2*wm1^4*x0 - b4*w0^2*w1^3*wm1^5 + b6*w0^4*w1^2*wm1^4 - be^2*w0^4*w1^2*wm1^4 + 4*w0^4*w1^2*wm1^4*x0^3 - 6*w0^2*w1^3*wm1^5*x0^2) * hc + (w0^2*w1^3*wm1^5) * hd + (w0^5*wm1^2*x0^2 - 2*w0^5*wm1^2*x0*xn + w0^5*wm1^2*xn^2) * hinv + (-c0*w0^4*w1^2*wm1^2*x0^2 + 2*c0*w0^4*w1^2*wm1^2*x0*xn - c0*w0^4*w1^2*wm1^2*xn^2) * hxm + (b2*c0*w0^2*w1^2*wm1^4*x0 + b4*c0*w0^2*w1^2*wm1^4 - be^4*w0^4*w1*wm1^3*x0 + be^4*w0^4*w1*wm1^3*xn - be^4*w0^2*w1^2*wm1^4 + be^2*c0*w0^6*wm1^2*x0 - be^2*c0*w0^6*wm1^2*xn + be^2*c0*w0^4*w1*wm1^3 + 6*c0*w0^2*w1^2*wm1^4*x0^2 - d0*w0^4*w1*wm1^3*x0 + d0*w0^4*w1*wm1^3*xn - d0*w0^2*w1^2*wm1^4) * hxn + (c0*w0^4*w1^2*wm1^4) * hS + (w0^2*w1^3*wm1^5*x0^2) * hb8

/- English proof (translation)
Use `eq_of_mul_sub_eq_zero (M := wm2 * wm3 ^ 2) (by simp [hwm2, hwm3]) ?_` and prove the remaining obligations. Take the linear combination `(b ^ 2 * w0 * wm3 ^ 2) * s0 + (-c * wm2 * (b ^ 2 * w0 * wm2 + wm3 * wp1)) * s1 + (-b ^ 4 * w0 ^ 2 * wm2) * s2 + (-b ^ 2 * w0 ^ 3) * s3`.
-/
private theorem step_alg_zero {b c wp2 wp1 w0 wm2 wm3 wm4 : F}
    (s0 : wp2 * wm2 = -c * w0 ^ 2) (s1 : wp1 * wm3 = b ^ 2 * w0 * wm2)
    (s2 : w0 * wm4 = -c * wm2 ^ 2) (s3 : 0 = b ^ 2 * wm2 * wm4 - c * wm3 ^ 2)
    (hwm2 : wm2 ≠ 0) (hwm3 : wm3 ≠ 0) :
    wp2 * w0 * b ^ 2 = c * wp1 ^ 2 := by
  refine eq_of_mul_sub_eq_zero (M := wm2 * wm3 ^ 2) (by simp [hwm2, hwm3]) ?_
  linear_combination (b ^ 2 * w0 * wm3 ^ 2) * s0 + (-c * wm2 * (b ^ 2 * w0 * wm2 + wm3 * wp1)) * s1 +
    (-b ^ 4 * w0 ^ 2 * wm2) * s2 + (-b ^ 2 * w0 ^ 3) * s3

end Algebra

section Points

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

def xOf : W.toAffine.Point → F
  | .zero => 0
  | .some x _ _ => x

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem xOf_some {x y : F} (h : W.toAffine.Nonsingular x y) : xOf W (.some x y h) = x := rfl

/- English proof (translation)
Consider the cases of `P with`. Consider the case `zero => exact absurd rfl hP`. Consider the case `some x y h => exact ⟨y, h, rfl⟩`. Use the proof step `@[simp]`.
-/
theorem exists_eq_some_xOf {P : W.toAffine.Point} (hP : P ≠ 0) :
    ∃ y h, P = .some (xOf W P) y h := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact ⟨y, h, rfl⟩

@[simp]
/- English proof (translation)
Consider the cases of `P with`. Consider the case `zero => rfl`. Consider the case `some x y h => rw [Point.neg_some, xOf_some, xOf_some]`.
-/
theorem xOf_neg (P : W.toAffine.Point) : xOf W (-P) = xOf W P := by
  cases P with
  | zero => rfl
  | some x y h => rw [Point.neg_some, xOf_some, xOf_some]

variable [DecidableEq F]

/- English proof (translation)
Establish `hs : Point.some x₁ y₁ h₁ - .some x₂ y₂ h₂ = .some x₁ y₁ h₁ + .some x₂ (W.toAffine.negY x₂ y₂) ((nonsingular_neg ..).mpr h₂)`. Rewrite using `[sub_eq_add_neg, Point.neg_some]`. Rewrite using `[hs, Point.add_of_X_ne hx, Point.add_of_X_ne hx]`. Use `⟨Point.some_ne_zero _, Point.some_ne_zero _, ?_⟩` and prove the remaining obligations. Simplify using `only [xOf_some]`.

Establish `hd : x₁ - x₂ ≠ 0` using `sub_ne_zero.mpr hx`. Establish `hl : W.toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂`. Rewrite using `[slope_of_X_ne hx, div_mul_cancel₀ _ hd]`. Establish `hlp : W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂) * (x₁ - x₂) = y₁ - (-y₂ - W.a₁ * x₂ - W.a₃)`. Rewrite using `[slope_of_X_ne hx, div_mul_cancel₀ _ hd, negY]`.

Use `set l := W.toAffine.slope x₁ x₂ y₁ y₂`. Use `set lp := W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)`. Establish `e1` using `(equation_iff _ _).mp h₁.1`. Establish `e2` using `(equation_iff _ _).mp h₂.1`. Use `eq_of_mul_sub_eq_zero (M := (x₁ - x₂) ^ 4) (pow_ne_zero _ hd) ?_` and prove the remaining obligations.

Simplify using `only [addX, b₂, b₄, b₆]`. Take the linear combination `((x₁ - x₂) ^ 4 * (W.a₁ * x₁ - W.a₁ * x₂ + l * x₁ - l * x₂ + y₁ - y₂)) * hl + ((x₁ - x₂) ^ 4 * (W.a₁ * x₁ + W.a₃ + lp * x₁ - lp * x₂ + y₁ + y₂)) * hlp + (2 * (x₁ - x₂) ^ 4) * e1 + (2 * (x₁ - x₂) ^ 4) * e2`.
-/
theorem xOf_add_add_xOf_sub {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    Point.some x₁ y₁ h₁ + .some x₂ y₂ h₂ ≠ 0 ∧ Point.some x₁ y₁ h₁ - .some x₂ y₂ h₂ ≠ 0 ∧
      (xOf W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) + xOf W (.some x₁ y₁ h₁ - .some x₂ y₂ h₂)) *
          (x₁ - x₂) ^ 2 =
        2 * x₁ * x₂ * (x₁ + x₂) + W.b₂ * x₁ * x₂ + W.b₄ * (x₁ + x₂) + W.b₆ := by
  have hs : Point.some x₁ y₁ h₁ - .some x₂ y₂ h₂ =
      .some x₁ y₁ h₁ + .some x₂ (W.toAffine.negY x₂ y₂) ((nonsingular_neg ..).mpr h₂) := by
    rw [sub_eq_add_neg, Point.neg_some]
  rw [hs, Point.add_of_X_ne hx, Point.add_of_X_ne hx]
  refine ⟨Point.some_ne_zero _, Point.some_ne_zero _, ?_⟩
  simp only [xOf_some]
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hl : W.toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
    rw [slope_of_X_ne hx, div_mul_cancel₀ _ hd]
  have hlp : W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂) * (x₁ - x₂) =
      y₁ - (-y₂ - W.a₁ * x₂ - W.a₃) := by
    rw [slope_of_X_ne hx, div_mul_cancel₀ _ hd, negY]
  set l := W.toAffine.slope x₁ x₂ y₁ y₂
  set lp := W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)
  have e1 := (equation_iff _ _).mp h₁.1
  have e2 := (equation_iff _ _).mp h₂.1
  refine eq_of_mul_sub_eq_zero (M := (x₁ - x₂) ^ 4) (pow_ne_zero _ hd) ?_
  simp only [addX, b₂, b₄, b₆]
  linear_combination ((x₁ - x₂) ^ 4 * (W.a₁ * x₁ - W.a₁ * x₂ + l * x₁ - l * x₂ + y₁ - y₂)) * hl +
    ((x₁ - x₂) ^ 4 * (W.a₁ * x₁ + W.a₃ + lp * x₁ - lp * x₂ + y₁ + y₂)) * hlp +
    (2 * (x₁ - x₂) ^ 4) * e1 + (2 * (x₁ - x₂) ^ 4) * e2

/- English proof (translation)
Establish `hiff : y = W.toAffine.negY x y ↔ 2 * y + W.a₁ * x + W.a₃ = 0`. Apply the tactic sequence `rw [negY]; constructor <;> intro h' <;> linear_combination h'`. Rewrite using `[two_zsmul]`. Distinguish the cases in `hb : 2 * y + W.a₁ * x + W.a₃ = 0`. Conclude with `⟨iff_of_true (Point.add_self_of_Y_eq (hiff.mpr hb)) hb, fun h' => absurd hb h'⟩`.

Establish `hy : y ≠ W.toAffine.negY x y` using `fun h' => hb (hiff.mp h')`. Rewrite using `[Point.add_self_of_Y_ne hy]`. Use `⟨iff_of_false (Point.some_ne_zero _) hb, fun _ => ?_⟩` and prove the remaining obligations. Simplify using `only [xOf_some]`. Establish `hl : W.toAffine.slope x x y y * (y - (-y - W.a₁ * x - W.a₃)) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y`.

Rewrite using `[slope_of_Y_ne rfl hy, negY, div_mul_cancel₀]`. Rewrite using `[show y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃ by ring]; exact hb`. Use `set l := W.toAffine.slope x x y y`. Establish `e` using `(equation_iff _ _).mp h.1`. Use `eq_of_mul_sub_eq_zero (M := (2 * y + W.a₁ * x + W.a₃) ^ 2) (pow_ne_zero _ hb) ?_` and prove the remaining obligations.

Rewrite using `[Psi3_eval]`. Simplify using `only [addX, b₂, b₄, b₆, b₈]`. Take the linear combination `((W.a₁ * x + W.a₃ + 2 * y) ^ 2 * (l * W.a₁ * x + l * W.a₃ + 2 * l * y + W.a₁ ^ 2 * x + W.a₁ * W.a₃ + W.a₁ * y + 2 * W.a₂ * x + W.a₄ + 3 * x ^ 2)) * hl + (-(W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * (W.a₁ * x + W.a₃ + 2 * y) ^ 2) * e`.
-/
theorem two_smul_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    ((2 : ℤ) • Point.some x y h = 0 ↔ 2 * y + W.a₁ * x + W.a₃ = 0) ∧
      (2 * y + W.a₁ * x + W.a₃ ≠ 0 →
        xOf W ((2 : ℤ) • Point.some x y h) * (2 * y + W.a₁ * x + W.a₃) ^ 2 =
          x * (2 * y + W.a₁ * x + W.a₃) ^ 2 - W.Ψ₃.eval x) := by
  have hiff : y = W.toAffine.negY x y ↔ 2 * y + W.a₁ * x + W.a₃ = 0 := by
    rw [negY]; constructor <;> intro h' <;> linear_combination h'
  rw [two_zsmul]
  by_cases hb : 2 * y + W.a₁ * x + W.a₃ = 0
  · exact ⟨iff_of_true (Point.add_self_of_Y_eq (hiff.mpr hb)) hb, fun h' => absurd hb h'⟩
  have hy : y ≠ W.toAffine.negY x y := fun h' => hb (hiff.mp h')
  rw [Point.add_self_of_Y_ne hy]
  refine ⟨iff_of_false (Point.some_ne_zero _) hb, fun _ => ?_⟩
  simp only [xOf_some]
  have hl : W.toAffine.slope x x y y * (y - (-y - W.a₁ * x - W.a₃)) =
      3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [slope_of_Y_ne rfl hy, negY, div_mul_cancel₀]
    rw [show y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃ by ring]; exact hb
  set l := W.toAffine.slope x x y y
  have e := (equation_iff _ _).mp h.1
  refine eq_of_mul_sub_eq_zero (M := (2 * y + W.a₁ * x + W.a₃) ^ 2) (pow_ne_zero _ hb) ?_
  rw [Psi3_eval]
  simp only [addX, b₂, b₄, b₆, b₈]
  linear_combination ((W.a₁ * x + W.a₃ + 2 * y) ^ 2 * (l * W.a₁ * x + l * W.a₃ + 2 * l * y +
      W.a₁ ^ 2 * x + W.a₁ * W.a₃ + W.a₁ * y + 2 * W.a₂ * x + W.a₄ + 3 * x ^ 2)) * hl +
    (-(W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * (W.a₁ * x + W.a₃ + 2 * y) ^ 2) * e

end Points

section Main

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
  {x₀ y₀ : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)

private def Good (n : ℤ) : Prop :=
  (n • Point.some x₀ y₀ h₀ = 0 ↔ psiAt W x₀ y₀ n = 0) ∧
    (psiAt W x₀ y₀ n ≠ 0 → xOf W (n • Point.some x₀ y₀ h₀) =
      x₀ - psiAt W x₀ y₀ (n + 1) * psiAt W x₀ y₀ (n - 1) / psiAt W x₀ y₀ n ^ 2)

/- English proof (translation)
Use `⟨iff_of_false (by rw [one_zsmul]; exact Point.some_ne_zero h₀) (by rw [psiAt_one]; exact one_ne_zero), fun _ => ?_⟩` and prove the remaining obligations. Rewrite using `[one_zsmul, xOf_some, show (1 : ℤ) - 1 = 0 by norm_num, psiAt_zero]`. Simplify using the standard rewrite rules.
-/
private theorem good_one : Good W h₀ 1 := by
  refine ⟨iff_of_false (by rw [one_zsmul]; exact Point.some_ne_zero h₀)
    (by rw [psiAt_one]; exact one_ne_zero), fun _ => ?_⟩
  rw [one_zsmul, xOf_some, show (1 : ℤ) - 1 = 0 by norm_num, psiAt_zero]
  simp

/- English proof (translation)
Take `⟨h1, h2⟩` from `two_smul_some W h₀`. Rewrite using `[Good, psiAt_two]`. Use `⟨h1, fun hb => ?_⟩` and prove the remaining obligations. Use `h2 hb` as an intermediate fact. Rewrite using `[show (2 : ℤ) + 1 = 3 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num, psiAt_three, psiAt_one, mul_one, eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', div_eq_iff (pow_ne_zero 2 hb)]`.

Take the linear combination `this`.
-/
private theorem good_two : Good W h₀ 2 := by
  obtain ⟨h1, h2⟩ := two_smul_some W h₀
  rw [Good, psiAt_two]
  refine ⟨h1, fun hb => ?_⟩
  have := h2 hb
  rw [show (2 : ℤ) + 1 = 3 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num, psiAt_three, psiAt_one,
    mul_one, eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', div_eq_iff (pow_ne_zero 2 hb)]
  linear_combination this

omit [DecidableEq F] in
include h₀ in

/- English proof (translation)
Establish `hb : 2 * y₀ + W.a₁ * x₀ + W.a₃ ≠ 0`. Introduce `hb`. Use `Psi3_eval_of_two_y W h₀.1 hb` as an intermediate fact. Rewrite `this` using `[hc, zero_eq_neg, pow_eq_zero_iff two_ne_zero]`. Break down `((nonsingular_iff' _ _).mp h₀).2 with h | h` into its components or cases.

Conclude with `h this`. Conclude with `h hb`. Use `⟨hb, fun hd => hb ?_⟩` and prove the remaining obligations. Use `two_y_pow_four_add W h₀.1` as an intermediate fact. Rewrite `this` using `[hc, hd, mul_zero, add_zero]`.

Conclude with `pow_eq_zero_iff (by norm_num) |>.mp this`.
-/
private theorem ne_zero_of_Psi3_eq_zero (hc : W.Ψ₃.eval x₀ = 0) :
    2 * y₀ + W.a₁ * x₀ + W.a₃ ≠ 0 ∧ W.preΨ₄.eval x₀ ≠ 0 := by
  have hb : 2 * y₀ + W.a₁ * x₀ + W.a₃ ≠ 0 := by
    intro hb
    have := Psi3_eval_of_two_y W h₀.1 hb
    rw [hc, zero_eq_neg, pow_eq_zero_iff two_ne_zero] at this
    rcases ((nonsingular_iff' _ _).mp h₀).2 with h | h
    · exact h this
    · exact h hb
  refine ⟨hb, fun hd => hb ?_⟩
  have := two_y_pow_four_add W h₀.1
  rw [hc, hd, mul_zero, add_zero] at this
  exact pow_eq_zero_iff (by norm_num) |>.mp this

/- English proof (translation)
Establish `g_n` using `ih n (by omega) le_rfl`. Establish `g_n1` using `ih (n - 1) (by omega) (by omega)`. Establish `g_n2 : 3 ≤ n → Good W h₀ (n - 2)` using `fun h => ih (n - 2) (by omega) (by omega)`. Establish `g_n3 : 4 ≤ n → Good W h₀ (n - 3)` using `fun h => ih (n - 3) (by omega) (by omega)`. Establish `somos` using `psiAt_somos W x₀ y₀`.

Establish `hinv` using `psiAt_invariant W x₀ y₀ n`. Establish `hE` using `h₀.1`. Establish `hbsq` using `two_y_sq W hE`. Establish `hc` using `Psi3_eval W x₀`. Establish `hd` using `prePsi4_eval W x₀`.

Establish `hP : Point.some x₀ y₀ h₀ ≠ 0` using `Point.some_ne_zero h₀`. Establish `xP : xOf W (Point.some x₀ y₀ h₀) = x₀` using `rfl`. Establish `e_succ : (n + 1) • Point.some x₀ y₀ h₀ = n • Point.some x₀ y₀ h₀ + Point.some x₀ y₀ h₀`. Rewrite using `[add_zsmul, one_zsmul]`. Establish `e_pred : (n - 1) • Point.some x₀ y₀ h₀ = n • Point.some x₀ y₀ h₀ - Point.some x₀ y₀ h₀`.

Rewrite using `[sub_zsmul, one_zsmul, sub_eq_add_neg]`. Establish `z3 : W.Ψ₃.eval x₀ = 0 → ∀ k, psiAt W x₀ y₀ k = 0 ↔ (3 : ℤ) ∣ k` using `fun hc0 k => by`. Take `⟨hb, hd⟩` from `ne_zero_of_Psi3_eq_zero W h₀ hc0`. Rewrite using `[psiAt_eq, hc0]`. Conclude with `normEDS_eq_zero_iff_of_three hb hd k`.

Establish `zev : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 → ∀ k, Even k → psiAt W x₀ y₀ k = 0` using `fun hb k hk => by rw [psiAt_eq, hb]; exact normEDS_zero_left_of_even _ _ hk`. Establish `nz3 : W.Ψ₃.eval x₀ = 0 → 2 * y₀ + W.a₁ * x₀ + W.a₃ ≠ 0` using `fun hc0 => (ne_zero_of_Psi3_eq_zero W h₀ hc0).1`. Take `⟨t1, t2⟩` from `two_smul_some W h₀`. Establish `psi1` using `psiAt_one W x₀ y₀`. Simplify using `only [Good] at g_n g_n1 g_n2 g_n3 ⊢`.

Rewrite `g_n1` using `[show n - 1 + 1 = n by ring, show n - 1 - 1 = n - 2 by ring]`. Rewrite using `[show n + 1 + 1 = n + 2 by ring, show n + 1 - 1 = n by ring]`. Generalize the expression as in `psiAt W x₀ y₀ = w at *`. Generalize the expression as in `W.Ψ₃.eval x₀ = c₀ at *`. Generalize the expression as in `2 * y₀ + W.a₁ * x₀ + W.a₃ = β at *`.

Distinguish the cases in `hwn : w n = 0`. Establish `hQ : n • Point.some x₀ y₀ h₀ = 0` using `g_n.1.mpr hwn`. Establish `e1 : (n + 1) • Point.some x₀ y₀ h₀ = Point.some x₀ y₀ h₀` using `by rw [e_succ, hQ, zero_add]`. Establish `hwp : w (n + 1) ≠ 0`. Distinguish the cases in `hc0 : c₀ = 0`.

Rewrite using `[ne_eq, z3 hc0]`. Rewrite `hwn` using `[z3 hc0]`. Use linear arithmetic over natural numbers and integers. Establish `hwm : w (n - 1) ≠ 0`. Introduce `h`.

Use `g_n1.1.mpr h` as an intermediate fact. Rewrite `this` using `[e_pred, hQ, zero_sub, neg_eq_zero]`. Conclude with `hP this`. Establish `s` using `somos (n - 1)`. Rewrite `s` using `[show n - 1 + 2 = n + 1 by ring, show n - 1 - 2 = n - 3 by ring, show n - 1 + 1 = n by ring, show n - 1 - 1 = n - 2 by ring, hwn]`.

Introduce `h`. Rewrite `s` using `[h, zero_mul, mul_zero, zero_mul, zero_sub, zero_eq_neg]`. Conclude with `mul_ne_zero hc0 (pow_ne_zero 2 hwm) s`. Use `⟨iff_of_false (by rw [e1]; exact hP) hwp, fun _ => ?_⟩` and prove the remaining obligations. Rewrite using `[e1, xP, hwn]`.

Simplify using the standard rewrite rules. Distinguish the cases in `hwn1 : w (n - 1) = 0`. Establish `hQ1 : (n - 1) • Point.some x₀ y₀ h₀ = 0` using `g_n1.1.mpr hwn1`. Establish `hQ : n • Point.some x₀ y₀ h₀ = Point.some x₀ y₀ h₀`. Rewrite `hQ1` using `[e_pred, sub_eq_zero]`.

Conclude with `hQ1`. Establish `e2 : (n + 1) • Point.some x₀ y₀ h₀ = (2 : ℤ) • Point.some x₀ y₀ h₀`. Rewrite using `[e_succ, hQ, two_zsmul]`. Establish `hn3 : 3 ≤ n`. Assume the negation of the conclusion as `h`.

Establish `: n = 2` using `by omega`. Rewrite `hwn1` using `[this, show (2 : ℤ) - 1 = 1 by norm_num, psi1]`. Conclude with `one_ne_zero hwn1`. Distinguish the cases in `hb : β = 0`. Establish `h2P : (2 : ℤ) • Point.some x₀ y₀ h₀ = 0` using `t1.mpr hb`.

Establish `hev : Even (n + 1)`. Break down `Int.even_or_odd (n - 1) with he | ho` into its components or cases. Rewrite using `[show n + 1 = n - 1 + 2 by ring]; exact he.add even_two`. It suffices to derive a contradiction. Take `⟨k, hk⟩` from `ho`.

Rewrite `hQ1` using `[hk, add_zsmul, one_zsmul, mul_comm, mul_zsmul, h2P, zsmul_zero, zero_add]`. Conclude with `hP hQ1`. Establish `hwp : w (n + 1) = 0` using `zev hb _ hev`. Conclude with `⟨iff_of_true (by rw [e2]; exact h2P) hwp, fun h => absurd hwp h⟩`. Establish `h2P : (2 : ℤ) • Point.some x₀ y₀ h₀ ≠ 0` using `fun h => hb (t1.mp h)`.

Establish `hwm2 : w (n - 2) ≠ 0`. Introduce `h`. Establish `g` using `((g_n2 hn3).1).mpr h`. Rewrite `g` using `[show n - 2 = n - 1 - 1 by ring, sub_zsmul, one_zsmul, hQ1, zero_add, neg_eq_zero]`. Conclude with `hP g`.

Establish `hn4 : 4 ≤ n`. Assume the negation of the conclusion as `h`. Establish `: n = 3` using `by omega`. Rewrite `hQ1` using `[this, show (3 : ℤ) - 1 = 2 by norm_num]`. Conclude with `h2P hQ1`.

Establish `hwm3 : w (n - 3) ≠ 0`. Introduce `h`. Establish `g` using `((g_n3 hn4).1).mpr h`. Rewrite `g` using `[show n - 3 = n - 1 - 2 by ring, sub_zsmul, hQ1, zero_add, neg_eq_zero]`. Conclude with `h2P g`.

Establish `s0` using `somos n`. Establish `s1` using `somos (n - 1)`. Establish `s2` using `somos (n - 2)`. Establish `s3` using `somos (n - 3)`. Rewrite `s1` using `[show n - 1 + 2 = n + 1 by ring, show n - 1 - 2 = n - 3 by ring, show n - 1 + 1 = n by ring, show n - 1 - 1 = n - 2 by ring]`.

Rewrite `s2` using `[show n - 2 + 2 = n by ring, show n - 2 - 2 = n - 4 by ring, show n - 2 + 1 = n - 1 by ring, show n - 2 - 1 = n - 3 by ring]`. Rewrite `s3` using `[show n - 3 + 2 = n - 1 by ring, show n - 3 - 2 = n - 5 by ring, show n - 3 + 1 = n - 2 by ring, show n - 3 - 1 = n - 4 by ring]`. Rewrite `s0`, `s1`, `s2`, `s3` using `[hwn1]`. Establish `hwp : w (n + 1) ≠ 0`. Introduce `h`.

Rewrite `s1` using `[h]`. Establish `: β ^ 2 * w n * w (n - 2) = 0` using `by linear_combination -s1`. Conclude with `mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hb) hwn) hwm2 this`. Establish `key` using `step_alg_zero (b := β) (c := c₀) (wp2 := w (n + 2)) (wp1 := w (n + 1)) (w0 := w n) (wm2 := w (n - 2)) (wm3 := w (n - 3)) (wm4 := w (n - 4)) (by linear_combination s0) (by linear_combination s1) (by linear_combination s2) (by linear_combination s3) hwm2 hwm3`. Use `⟨iff_of_false (by rw [e2]; exact h2P) hwp, fun _ => ?_⟩` and prove the remaining obligations.

Establish `hx2` using `t2 hb`. Rewrite using `[e2, eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', div_eq_iff (pow_ne_zero 2 hwp)]`. Apply `mul_right_cancel₀ (pow_ne_zero 2 hb)` to reduce the goal to its premises. Take the linear combination `key + w (n + 1) ^ 2 * hx2`. Establish `hQ : n • Point.some x₀ y₀ h₀ ≠ 0` using `fun h => hwn (g_n.1.mp h)`.

Establish `hQ1 : (n - 1) • Point.some x₀ y₀ h₀ ≠ 0` using `fun h => hwn1 (g_n1.1.mp h)`. Establish `xn` using `g_n.2 hwn`. Establish `xm` using `g_n1.2 hwn1`. Take `⟨yn, hn', hQeq⟩` from `exists_eq_some_xOf W hQ`. Distinguish the cases in `hwp : w (n + 1) = 0`.

Establish `hx : xOf W (n • Point.some x₀ y₀ h₀) = x₀` using `by rw [xn, hwp]; simp`. Use `(Point.X_eq_iff (h₁ := hn') (h₂ := h₀)).mp hx` as an intermediate fact. Rewrite `this` using `[← hQeq]`. Break down `this with h | h` into its components or cases. Conclude with `absurd (by rw [e_pred, h, sub_self]) hQ1`.

Conclude with `⟨iff_of_true (by rw [e_succ, h, neg_add_cancel]) hwp, fun h' => absurd hwp h'⟩`. Establish `hc0 : c₀ ≠ 0`. Introduce `hc0`. Rewrite `hwn`, `hwn1`, `hwp` using `[z3 hc0]`. Use linear arithmetic over natural numbers and integers.

Establish `hxne : xOf W (n • Point.some x₀ y₀ h₀) - x₀ ≠ 0`. Rewrite using `[xn, sub_sub_cancel_left, neg_ne_zero]`. Conclude with `div_ne_zero (mul_ne_zero hwp hwn1) (pow_ne_zero 2 hwn)`. Establish `hx : xOf W (n • Point.some x₀ y₀ h₀) ≠ x₀` using `sub_ne_zero.mp hxne`. Rewrite `hx` using `[hQeq]`.

Take `⟨hne1, -, hsum⟩` from `xOf_add_add_xOf_sub W hn' h₀ hx`. Rewrite `hsum` using `[← hQeq, ← e_succ, ← e_pred]`. Rewrite `hne1` using `[← hQeq, ← e_succ]`. Use `⟨iff_of_false hne1 hwp, fun _ => ?_⟩` and prove the remaining obligations. Establish `hxm : xOf W ((n - 1) • Point.some x₀ y₀ h₀) * w (n - 1) ^ 2 = x₀ * w (n - 1) ^ 2 - w n * w (n - 2)`.

Rewrite using `[xm, sub_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hwn1)]`. Establish `hxn : xOf W (n • Point.some x₀ y₀ h₀) * w n ^ 2 = x₀ * w n ^ 2 - w (n + 1) * w (n - 1)`. Rewrite using `[xn, sub_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hwn)]`. Establish `key` using `step_alg W.b_relation hbsq hc hd hinv hxm hxn hsum hc0 hwn hwn1 hxne`. Rewrite using `[eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', div_eq_iff (pow_ne_zero 2 hwp)]`.

Take the linear combination `key`.
-/
private theorem good_succ (n : ℤ) (hn : 2 ≤ n) (ih : ∀ j, 1 ≤ j → j ≤ n → Good W h₀ j) :
    Good W h₀ (n + 1) := by
  have g_n := ih n (by omega) le_rfl
  have g_n1 := ih (n - 1) (by omega) (by omega)
  have g_n2 : 3 ≤ n → Good W h₀ (n - 2) := fun h => ih (n - 2) (by omega) (by omega)
  have g_n3 : 4 ≤ n → Good W h₀ (n - 3) := fun h => ih (n - 3) (by omega) (by omega)
  have somos := psiAt_somos W x₀ y₀
  have hinv := psiAt_invariant W x₀ y₀ n
  have hE := h₀.1
  have hbsq := two_y_sq W hE
  have hc := Psi3_eval W x₀
  have hd := prePsi4_eval W x₀
  have hP : Point.some x₀ y₀ h₀ ≠ 0 := Point.some_ne_zero h₀
  have xP : xOf W (Point.some x₀ y₀ h₀) = x₀ := rfl
  have e_succ : (n + 1) • Point.some x₀ y₀ h₀ = n • Point.some x₀ y₀ h₀ + Point.some x₀ y₀ h₀ := by
    rw [add_zsmul, one_zsmul]
  have e_pred : (n - 1) • Point.some x₀ y₀ h₀ = n • Point.some x₀ y₀ h₀ - Point.some x₀ y₀ h₀ := by
    rw [sub_zsmul, one_zsmul, sub_eq_add_neg]
  have z3 : W.Ψ₃.eval x₀ = 0 → ∀ k, psiAt W x₀ y₀ k = 0 ↔ (3 : ℤ) ∣ k := fun hc0 k => by
    obtain ⟨hb, hd⟩ := ne_zero_of_Psi3_eq_zero W h₀ hc0
    rw [psiAt_eq, hc0]; exact normEDS_eq_zero_iff_of_three hb hd k
  have zev : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 → ∀ k, Even k → psiAt W x₀ y₀ k = 0 :=
    fun hb k hk => by rw [psiAt_eq, hb]; exact normEDS_zero_left_of_even _ _ hk
  have nz3 : W.Ψ₃.eval x₀ = 0 → 2 * y₀ + W.a₁ * x₀ + W.a₃ ≠ 0 :=
    fun hc0 => (ne_zero_of_Psi3_eq_zero W h₀ hc0).1
  obtain ⟨t1, t2⟩ := two_smul_some W h₀
  have psi1 := psiAt_one W x₀ y₀
  simp only [Good] at g_n g_n1 g_n2 g_n3 ⊢
  rw [show n - 1 + 1 = n by ring, show n - 1 - 1 = n - 2 by ring] at g_n1
  rw [show n + 1 + 1 = n + 2 by ring, show n + 1 - 1 = n by ring]
  generalize psiAt W x₀ y₀ = w at *
  generalize W.Ψ₃.eval x₀ = c₀ at *
  generalize 2 * y₀ + W.a₁ * x₀ + W.a₃ = β at *
  by_cases hwn : w n = 0
  ·
    have hQ : n • Point.some x₀ y₀ h₀ = 0 := g_n.1.mpr hwn
    have e1 : (n + 1) • Point.some x₀ y₀ h₀ = Point.some x₀ y₀ h₀ := by rw [e_succ, hQ, zero_add]
    have hwp : w (n + 1) ≠ 0 := by
      by_cases hc0 : c₀ = 0
      · rw [ne_eq, z3 hc0]
        rw [z3 hc0] at hwn
        omega
      · have hwm : w (n - 1) ≠ 0 := by
          intro h
          have := g_n1.1.mpr h
          rw [e_pred, hQ, zero_sub, neg_eq_zero] at this
          exact hP this
        have s := somos (n - 1)
        rw [show n - 1 + 2 = n + 1 by ring, show n - 1 - 2 = n - 3 by ring,
          show n - 1 + 1 = n by ring, show n - 1 - 1 = n - 2 by ring, hwn] at s
        intro h
        rw [h, zero_mul, mul_zero, zero_mul, zero_sub, zero_eq_neg] at s
        exact mul_ne_zero hc0 (pow_ne_zero 2 hwm) s
    refine ⟨iff_of_false (by rw [e1]; exact hP) hwp, fun _ => ?_⟩
    rw [e1, xP, hwn]
    simp
  by_cases hwn1 : w (n - 1) = 0
  ·
    have hQ1 : (n - 1) • Point.some x₀ y₀ h₀ = 0 := g_n1.1.mpr hwn1
    have hQ : n • Point.some x₀ y₀ h₀ = Point.some x₀ y₀ h₀ := by
      rw [e_pred, sub_eq_zero] at hQ1; exact hQ1
    have e2 : (n + 1) • Point.some x₀ y₀ h₀ = (2 : ℤ) • Point.some x₀ y₀ h₀ := by
      rw [e_succ, hQ, two_zsmul]
    have hn3 : 3 ≤ n := by
      by_contra h
      have : n = 2 := by omega
      rw [this, show (2 : ℤ) - 1 = 1 by norm_num, psi1] at hwn1
      exact one_ne_zero hwn1
    by_cases hb : β = 0
    · have h2P : (2 : ℤ) • Point.some x₀ y₀ h₀ = 0 := t1.mpr hb
      have hev : Even (n + 1) := by
        rcases Int.even_or_odd (n - 1) with he | ho
        · rw [show n + 1 = n - 1 + 2 by ring]; exact he.add even_two
        · exfalso
          obtain ⟨k, hk⟩ := ho
          rw [hk, add_zsmul, one_zsmul, mul_comm, mul_zsmul, h2P, zsmul_zero, zero_add] at hQ1
          exact hP hQ1
      have hwp : w (n + 1) = 0 := zev hb _ hev
      exact ⟨iff_of_true (by rw [e2]; exact h2P) hwp, fun h => absurd hwp h⟩
    · have h2P : (2 : ℤ) • Point.some x₀ y₀ h₀ ≠ 0 := fun h => hb (t1.mp h)
      have hwm2 : w (n - 2) ≠ 0 := by
        intro h
        have g := ((g_n2 hn3).1).mpr h
        rw [show n - 2 = n - 1 - 1 by ring, sub_zsmul, one_zsmul, hQ1, zero_add,
          neg_eq_zero] at g
        exact hP g
      have hn4 : 4 ≤ n := by
        by_contra h
        have : n = 3 := by omega
        rw [this, show (3 : ℤ) - 1 = 2 by norm_num] at hQ1
        exact h2P hQ1
      have hwm3 : w (n - 3) ≠ 0 := by
        intro h
        have g := ((g_n3 hn4).1).mpr h
        rw [show n - 3 = n - 1 - 2 by ring, sub_zsmul, hQ1, zero_add, neg_eq_zero] at g
        exact h2P g
      have s0 := somos n
      have s1 := somos (n - 1)
      have s2 := somos (n - 2)
      have s3 := somos (n - 3)
      rw [show n - 1 + 2 = n + 1 by ring, show n - 1 - 2 = n - 3 by ring,
        show n - 1 + 1 = n by ring, show n - 1 - 1 = n - 2 by ring] at s1
      rw [show n - 2 + 2 = n by ring, show n - 2 - 2 = n - 4 by ring,
        show n - 2 + 1 = n - 1 by ring, show n - 2 - 1 = n - 3 by ring] at s2
      rw [show n - 3 + 2 = n - 1 by ring, show n - 3 - 2 = n - 5 by ring,
        show n - 3 + 1 = n - 2 by ring, show n - 3 - 1 = n - 4 by ring] at s3
      rw [hwn1] at s0 s1 s2 s3
      have hwp : w (n + 1) ≠ 0 := by
        intro h
        rw [h] at s1
        have : β ^ 2 * w n * w (n - 2) = 0 := by linear_combination -s1
        exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hb) hwn) hwm2 this
      have key := step_alg_zero (b := β) (c := c₀) (wp2 := w (n + 2)) (wp1 := w (n + 1))
        (w0 := w n) (wm2 := w (n - 2)) (wm3 := w (n - 3)) (wm4 := w (n - 4))
        (by linear_combination s0) (by linear_combination s1) (by linear_combination s2)
        (by linear_combination s3) hwm2 hwm3
      refine ⟨iff_of_false (by rw [e2]; exact h2P) hwp, fun _ => ?_⟩
      have hx2 := t2 hb
      rw [e2, eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', div_eq_iff (pow_ne_zero 2 hwp)]
      apply mul_right_cancel₀ (pow_ne_zero 2 hb)
      linear_combination key + w (n + 1) ^ 2 * hx2

  have hQ : n • Point.some x₀ y₀ h₀ ≠ 0 := fun h => hwn (g_n.1.mp h)
  have hQ1 : (n - 1) • Point.some x₀ y₀ h₀ ≠ 0 := fun h => hwn1 (g_n1.1.mp h)
  have xn := g_n.2 hwn
  have xm := g_n1.2 hwn1
  obtain ⟨yn, hn', hQeq⟩ := exists_eq_some_xOf W hQ
  by_cases hwp : w (n + 1) = 0
  ·
    have hx : xOf W (n • Point.some x₀ y₀ h₀) = x₀ := by rw [xn, hwp]; simp
    have := (Point.X_eq_iff (h₁ := hn') (h₂ := h₀)).mp hx
    rw [← hQeq] at this
    rcases this with h | h
    · exact absurd (by rw [e_pred, h, sub_self]) hQ1
    · exact ⟨iff_of_true (by rw [e_succ, h, neg_add_cancel]) hwp, fun h' => absurd hwp h'⟩
  have hc0 : c₀ ≠ 0 := by
    intro hc0
    rw [z3 hc0] at hwn hwn1 hwp
    omega
  have hxne : xOf W (n • Point.some x₀ y₀ h₀) - x₀ ≠ 0 := by
    rw [xn, sub_sub_cancel_left, neg_ne_zero]
    exact div_ne_zero (mul_ne_zero hwp hwn1) (pow_ne_zero 2 hwn)
  have hx : xOf W (n • Point.some x₀ y₀ h₀) ≠ x₀ := sub_ne_zero.mp hxne
  rw [hQeq] at hx
  obtain ⟨hne1, -, hsum⟩ := xOf_add_add_xOf_sub W hn' h₀ hx
  rw [← hQeq, ← e_succ, ← e_pred] at hsum
  rw [← hQeq, ← e_succ] at hne1
  refine ⟨iff_of_false hne1 hwp, fun _ => ?_⟩
  have hxm : xOf W ((n - 1) • Point.some x₀ y₀ h₀) * w (n - 1) ^ 2 =
      x₀ * w (n - 1) ^ 2 - w n * w (n - 2) := by
    rw [xm, sub_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hwn1)]
  have hxn : xOf W (n • Point.some x₀ y₀ h₀) * w n ^ 2 = x₀ * w n ^ 2 - w (n + 1) * w (n - 1) := by
    rw [xn, sub_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hwn)]
  have key := step_alg W.b_relation hbsq hc hd hinv hxm hxn hsum hc0 hwn hwn1 hxne
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', div_eq_iff (pow_ne_zero 2 hwp)]
  linear_combination key

end Main

section Statements

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
  {x₀ y₀ : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => intro n h1 h2`. Use linear arithmetic over natural numbers and integers. Consider the case `succ N ih`. Introduce `n h1 h2`.

Break down `lt_or_eq_of_le h2 with h | h` into its components or cases. Conclude with `ih n h1 (by push_cast at h; omega)`. Break down `(by omega : n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | h3` into its components or cases. Conclude with `good_one W h₀`. Conclude with `good_two W h₀`.

Use `good_succ W h₀ (n - 1) (by omega) (fun j hj1 hj2 => ih j hj1 (by push_cast at h; omega))` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.
-/
private theorem good_nat (N : ℕ) : ∀ n : ℤ, 1 ≤ n → n ≤ N → Good W h₀ n := by
  induction N with
  | zero => intro n h1 h2; omega
  | succ N ih =>
    intro n h1 h2
    rcases lt_or_eq_of_le h2 with h | h
    · exact ih n h1 (by push_cast at h; omega)
    · rcases (by omega : n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | h3
      · exact good_one W h₀
      · exact good_two W h₀
      · have := good_succ W h₀ (n - 1) (by omega)
          (fun j hj1 hj2 => ih j hj1 (by push_cast at h; omega))
        rwa [sub_add_cancel] at this

/- English proof (translation)
Break down `lt_trichotomy n 0 with hn | rfl | hn` into its components or cases. Take `⟨g1, g2⟩` from `good_nat W h₀ (-n).toNat (-n) (by omega) (by omega)`. Simplify using `only [Good, neg_zsmul, neg_eq_zero, psiAt_neg] at g1 g2 ⊢`. Use `⟨g1, fun hw => ?_⟩` and prove the remaining obligations. Use `g2 (neg_ne_zero.mpr hw)` as an intermediate fact.

Rewrite `this` using `[xOf_neg]`. Rewrite using `[this, show -n + 1 = -(n - 1) by ring, show -n - 1 = -(n + 1) by ring, psiAt_neg, psiAt_neg]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨iff_of_true (zero_zsmul _) (psiAt_zero ..), fun h => absurd (psiAt_zero ..) h⟩` and prove the remaining obligations. Conclude with `good_nat W h₀ n.toNat n hn (by omega)`.
-/
private theorem good (n : ℤ) : Good W h₀ n := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · obtain ⟨g1, g2⟩ := good_nat W h₀ (-n).toNat (-n) (by omega) (by omega)
    simp only [Good, neg_zsmul, neg_eq_zero, psiAt_neg] at g1 g2 ⊢
    refine ⟨g1, fun hw => ?_⟩
    have := g2 (neg_ne_zero.mpr hw)
    rw [xOf_neg] at this
    rw [this, show -n + 1 = -(n - 1) by ring, show -n - 1 = -(n + 1) by ring, psiAt_neg,
      psiAt_neg]
    ring
  · refine ⟨iff_of_true (zero_zsmul _) (psiAt_zero ..), fun h => absurd (psiAt_zero ..) h⟩
  · exact good_nat W h₀ n.toNat n hn (by omega)

omit [DecidableEq F] in
include h₀ in

/- English proof (translation)
Rewrite using `[← psiAt_sq W h₀.1, pow_eq_zero_iff two_ne_zero]`.
-/
theorem psiAt_eq_zero_iff (n : ℤ) : psiAt W x₀ y₀ n = 0 ↔ (W.ΨSq n).eval x₀ = 0 := by
  rw [← psiAt_sq W h₀.1, pow_eq_zero_iff two_ne_zero]

/- English proof (translation)
Rewrite using `[(good W h₀ n).1, psiAt_eq_zero_iff W h₀]`.
-/
theorem zsmul_eq_zero_iff (n : ℤ) :
    n • Point.some x₀ y₀ h₀ = 0 ↔ (W.ΨSq n).eval x₀ = 0 := by
  rw [(good W h₀ n).1, psiAt_eq_zero_iff W h₀]

/- English proof (translation)
Establish `hw : psiAt W x₀ y₀ n ≠ 0` using `fun h => hn ((psiAt_eq_zero_iff W h₀ n).mp h)`. Rewrite using `[(good W h₀ n).2 hw, Phi_eval W h₀.1, ← psiAt_sq W h₀.1, sub_div, mul_div_cancel_right₀ _ (pow_ne_zero 2 hw)]`.
-/
theorem xOf_zsmul (n : ℤ) (hn : (W.ΨSq n).eval x₀ ≠ 0) :
    xOf W (n • Point.some x₀ y₀ h₀) = (W.Φ n).eval x₀ / (W.ΨSq n).eval x₀ := by
  have hw : psiAt W x₀ y₀ n ≠ 0 := fun h => hn ((psiAt_eq_zero_iff W h₀ n).mp h)
  rw [(good W h₀ n).2 hw, Phi_eval W h₀.1, ← psiAt_sq W h₀.1, sub_div,
    mul_div_cancel_right₀ _ (pow_ne_zero 2 hw)]

end Statements

end GroundTheory.Arith.Abelian
