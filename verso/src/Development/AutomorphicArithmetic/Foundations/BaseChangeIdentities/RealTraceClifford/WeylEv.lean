import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

/- English proof (translation)
Simplify using `[evT, ex, AddMonoidAlgebra.lift_single]`.
-/
private theorem evT_ex' {n : ℕ} (θ x : Wt n) :
    evT θ (ex x) = Complex.exp (Complex.I * ∑ a, (θ a : ℂ) * (x a : ℂ)) := by
  simp [evT, ex, AddMonoidAlgebra.lift_single]

/- English proof (translation)
Rewrite using `[← Matrix.det_transpose, Matrix.det_apply]`. Simplify using `only [alt, map_sum, map_smul, evT_ex', smul_eq_mul, sg, Matrix.transpose_apply, Matrix.of_apply]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[← Complex.exp_sum, Units.smul_def, zsmul_eq_mul, Finset.mul_sum]`. Both sides reduce to the same expression.
-/
private theorem evT_alt' {n : ℕ} (θ x : Wt n) :
    evT θ (alt x) = (Matrix.of fun a b : Fin n => Complex.exp (Complex.I * ((θ a : ℂ) * (x b : ℂ)))).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [alt, map_sum, map_smul, evT_ex', smul_eq_mul, sg, Matrix.transpose_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Complex.exp_sum, Units.smul_def, zsmul_eq_mul, Finset.mul_sum]
  rfl

/- English proof (translation)
Establish `e : (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))) = (Matrix.vandermonde z).submatrix id Fin.revPerm`. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e, Matrix.det_permute']`. Use `mul_ne_zero ?_ (Matrix.det_vandermonde_ne_zero_iff.mpr hz)` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> simp [h]`.
-/
private theorem den_ne {n : ℕ} (z : Fin n → ℂ) (hz : Function.Injective z) :
    (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det ≠ 0 := by
  have e : (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde z).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  rw [e, Matrix.det_permute']
  refine mul_ne_zero ?_ (Matrix.det_vandermonde_ne_zero_iff.mpr hz)
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> simp [h]

/- English proof (translation)
Use `set c : Fin n → ℂ := fun a => Complex.exp (Complex.I * (θ a : ℂ) * ((1 - (n : ℂ)) / 2)) with hc`. Establish `hcast : ∀ b : Fin n, (((n - 1 - (b : ℕ) : ℕ) : ℂ)) = (n : ℂ) - 1 - ((b : ℕ) : ℂ)`. Introduce `b`. Use `b.isLt` as an intermediate fact. Rewrite using `[Nat.cast_sub (by omega), Nat.cast_sub (by omega)]`.

Simplify using the standard rewrite rules. Establish `hD : evT θ (alt (rhoV n)) = (∏ a, c a) * (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det`. Rewrite using `[evT_alt', ← Matrix.det_mul_column]`. Use `congr 1`. Use extensionality with `a b`.

Simplify using `only [Matrix.of_apply, hz a, rhoV, c]`. Rewrite using `[← Complex.exp_nat_mul, ← Complex.exp_add, hcast b]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hA : evT θ (alt ((fun a => (lam a : ℝ)) + rhoV n)) = (∏ a, c a) * (Matrix.of fun i j : Fin n => z i ^ (lam j + ((n - 1 - (j : ℕ) : ℕ) : ℤ))).det`. Rewrite using `[evT_alt', ← Matrix.det_mul_column]`. Use `congr 1`. Use extensionality with `a b`. Simplify using `only [Matrix.of_apply, hz a, rhoV, c, Pi.add_apply]`.

Rewrite using `[← Complex.exp_int_mul, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Rewrite using `[hcast b]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hD, hA, weylChar]`. Establish `hden` using `den_ne z hinj`. Clear the denominators using the available nonvanishing facts.
-/
private theorem first' {n : ℕ} (lam : Fin n → ℤ) (θ : Wt n) (z : Fin n → ℂ)
    (hz : ∀ a, z a = Complex.exp (Complex.I * θ a)) (hinj : Function.Injective z) :
    weylChar lam z * evT θ (alt (rhoV n)) = evT θ (alt ((fun a => (lam a : ℝ)) + rhoV n)) := by
  set c : Fin n → ℂ := fun a => Complex.exp (Complex.I * (θ a : ℂ) * ((1 - (n : ℂ)) / 2)) with hc
  have hcast : ∀ b : Fin n, (((n - 1 - (b : ℕ) : ℕ) : ℂ)) = (n : ℂ) - 1 - ((b : ℕ) : ℂ) := by
    intro b
    have := b.isLt
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    simp
  have hD : evT θ (alt (rhoV n)) =
      (∏ a, c a) * (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det := by
    rw [evT_alt', ← Matrix.det_mul_column]
    congr 1
    ext a b
    simp only [Matrix.of_apply, hz a, rhoV, c]
    rw [← Complex.exp_nat_mul, ← Complex.exp_add, hcast b]
    congr 1
    push_cast
    ring
  have hA : evT θ (alt ((fun a => (lam a : ℝ)) + rhoV n)) =
      (∏ a, c a) * (Matrix.of fun i j : Fin n => z i ^ (lam j + ((n - 1 - (j : ℕ) : ℕ) : ℤ))).det := by
    rw [evT_alt', ← Matrix.det_mul_column]
    congr 1
    ext a b
    simp only [Matrix.of_apply, hz a, rhoV, c, Pi.add_apply]
    rw [← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    rw [hcast b]
    ring
  rw [hD, hA, weylChar]
  have hden := den_ne z hinj
  field_simp

/- English proof (translation)
Introduce `n lam θ z hz`. Use `⟨first' lam θ z hz, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `hinj2`. Establish `h` using `first' lam ((2 : ℝ) • θ) (fun a => z a ^ 2) (fun a => by`. Rewrite using `[hz a, ← Complex.exp_nat_mul]`.

Use `congr 1`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Use `push_cast`. Use the proof step `ring) hinj2`. Establish `e1 : evT θ (alt ((2 : ℝ) • rhoV n)) = evT ((2 : ℝ) • θ) (alt (rhoV n))`.

Rewrite using `[evT_alt', evT_alt']`. Use `congr 1`. Use extensionality with `a b`. Simplify using `only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : evT θ (alt (twoL lam)) = evT ((2 : ℝ) • θ) (alt ((fun a => (lam a : ℝ)) + rhoV n))`. Rewrite using `[evT_alt', evT_alt']`. Use `congr 1`.

Use extensionality with `a b`. Simplify using `only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, twoL]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, e2]`. Conclude with `h`. Simplify using `only [map_prod, map_add, map_one, evT_ex']`. Use `Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `congr 1`.

Rewrite using `[hz a, hz b, ← Complex.exp_sub]`. Use `congr 1`. Simplify using `only [rt, Pi.sub_apply, Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Introduce `y`. Simplify using `only [weylChar, map_div₀, RingHom.map_det, RingHom.mapMatrix_apply]`.

Apply the tactic sequence `congr 1 <;> congr 1 <;> ext i j <;> simp [map_zpow₀]`.
-/
theorem UpperTheory.RealTr.weylEv :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (θ : Wt n) (z : Fin n → ℂ), (∀ a, z a = Complex.exp (Complex.I * θ a)) →
      (Function.Injective z → weylChar lam z * evT θ (alt (rhoV n)) = evT θ (alt ((fun a => (lam a : ℝ)) + rhoV n))) ∧
      ((Function.Injective fun a => z a ^ 2) → weylChar lam (fun a => z a ^ 2) * evT θ (alt ((2 : ℝ) • rhoV n)) = evT θ (alt (twoL lam))) ∧
      ∏ a, ∏ b, (1 + z a / z b) = evT θ (∏ a, ∏ b, (1 + ex (rt a b))) ∧
      ∀ y : Fin n → ℂ, conj (weylChar lam fun a => conj (y a)) = weylChar lam y := by
  intro n lam θ z hz
  refine ⟨first' lam θ z hz, ?_, ?_, ?_⟩
  · intro hinj2
    have h := first' lam ((2 : ℝ) • θ) (fun a => z a ^ 2) (fun a => by
      rw [hz a, ← Complex.exp_nat_mul]
      congr 1
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      ring) hinj2
    have e1 : evT θ (alt ((2 : ℝ) • rhoV n)) = evT ((2 : ℝ) • θ) (alt (rhoV n)) := by
      rw [evT_alt', evT_alt']
      congr 1
      ext a b
      simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      congr 1
      push_cast
      ring
    have e2 : evT θ (alt (twoL lam)) = evT ((2 : ℝ) • θ) (alt ((fun a => (lam a : ℝ)) + rhoV n)) := by
      rw [evT_alt', evT_alt']
      congr 1
      ext a b
      simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, twoL]
      congr 1
      push_cast
      ring
    rw [e1, e2]
    exact h
  · simp only [map_prod, map_add, map_one, evT_ex']
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
    congr 1
    rw [hz a, hz b, ← Complex.exp_sub]
    congr 1
    simp only [rt, Pi.sub_apply, Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib, Pi.single_apply,
      apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro y
    simp only [weylChar, map_div₀, RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1 <;> congr 1 <;> ext i j <;> simp [map_zpow₀]
