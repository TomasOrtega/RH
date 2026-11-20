import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GWickA

noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

/- English proof (translation)
Simplify using `only [gramX, Qp, Qb, map_sub, map_sum, map_mul, evX, eval_X, if_true, Bool.false_eq_true, if_false]`. Rewrite using `[Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `cases h : ε a <;> simp [sgn, h]`.
-/
theorem gramX_apply (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramX ε x i j = ∑ a, sgn ε a * star (x a i) * x a j := by
  simp only [gramX, Qp, Qb, map_sub, map_sum, map_mul, evX, eval_X, if_true, Bool.false_eq_true, if_false]
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases h : ε a <;> simp [sgn, h]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [conjTranspose_apply, gramX_apply, star_sum, star_mul', star_star]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `have : star (sgn ε a) = sgn ε a := by unfold sgn; split_ifs <;> simp`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gramX_herm (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : (gramX ε x)ᴴ = gramX ε x := by
  ext i j
  simp only [conjTranspose_apply, gramX_apply, star_sum, star_mul', star_star]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : star (sgn ε a) = sgn ε a := by unfold sgn; split_ifs <;> simp
  rw [this]; ring

/- English proof (translation)
Establish `h : star (b * gramX ε x).trace = (b * gramX ε x).trace`. Rewrite using `[← trace_conjTranspose, conjTranspose_mul, gramX_herm, hb.eq, trace_mul_comm]`. Use `congrArg Complex.im h` as an intermediate fact. Simplify using `only [Complex.star_def, Complex.conj_im] at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem trace_im_zero (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian)
    (x : Fin m → Fin n → ℂ) : (b * gramX ε x).trace.im = 0 := by
  have h : star (b * gramX ε x).trace = (b * gramX ε x).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, gramX_herm, hb.eq, trace_mul_comm]
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

/- English proof (translation)
Rewrite using `[Complex.norm_exp]`. Establish `h` using `trace_im_zero ε b hb x`. Simplify using `[Complex.mul_re, h]`.
-/
theorem norm_exp_tr (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian)
    (x : Fin m → Fin n → ℂ) : ‖Complex.exp (Complex.I * t * (b * gramX ε x).trace)‖ = 1 := by
  rw [Complex.norm_exp]
  have h := trace_im_zero ε b hb x
  simp [Complex.mul_re, h]

def phiP (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) : PX m n :=
  -∑ a, ∑ k, ∑ j, C ((Amat ε c t b a) k j) * X (a, k, true) * X (a, j, false)

/- English proof (translation)
Simplify using `[phiP, evX]`.
-/
theorem evX_phiP (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    evX (phiP ε c t b) x = -∑ a, ∑ k, ∑ j, (Amat ε c t b a) k j * star (x a k) * x a j := by
  simp [phiP, evX]

/- English proof (translation)
Rewrite using `[gs, ← Complex.exp_add, evX_phiP]`. Use `congr 1`. Establish `h1 : (((c * ∑ a, ∑ i, ‖x a i‖ ^ 2 : ℝ)) : ℂ) = ∑ a, ∑ k, (c : ℂ) * (star (x a k) * x a k)`. Use `push_cast`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hz : (starRingEnd ℂ) (x a k) * x a k = ((‖x a k‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Rewrite using `[Complex.star_def, hz]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (b * gramX ε x).trace = ∑ a, ∑ k, ∑ j, sgn ε a * b j k * star (x a k) * x a j`. Simplify using `only [trace, diag, mul_apply, gramX_apply, Finset.mul_sum]`.

Use `conv_lhs => arg 2`. Use extensionality with `j`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ∀ a k, ∑ j, (Amat ε c t b a) k j * star (x a k) * x a j = (c : ℂ) * (star (x a k) * x a k) - ∑ j, Complex.I * t * (sgn ε a * b j k * star (x a k) * x a j)`. Introduce `a k`.

Simplify using `only [Amat, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]`. Use `congr 1`. Simplify using `[Finset.sum_ite_eq, mul_assoc]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1, h2]`. Simplify using `only [h3, Finset.sum_sub_distrib, Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_phiP (ε : Fin m → Bool) (c t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace) = Complex.exp (evX (phiP ε c t b) x) := by
  rw [gs, ← Complex.exp_add, evX_phiP]
  congr 1
  have h1 : (((c * ∑ a, ∑ i, ‖x a i‖ ^ 2 : ℝ)) : ℂ) = ∑ a, ∑ k, (c : ℂ) * (star (x a k) * x a k) := by
    push_cast
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
    have hz : (starRingEnd ℂ) (x a k) * x a k = ((‖x a k‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.star_def, hz]; push_cast; ring
  have h2 : (b * gramX ε x).trace = ∑ a, ∑ k, ∑ j, sgn ε a * b j k * star (x a k) * x a j := by
    simp only [trace, diag, mul_apply, gramX_apply, Finset.mul_sum]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 : ∀ a k, ∑ j, (Amat ε c t b a) k j * star (x a k) * x a j =
      (c : ℂ) * (star (x a k) * x a k) - ∑ j, Complex.I * t * (sgn ε a * b j k * star (x a k) * x a j) := by
    intro a k
    simp only [Amat, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply, smul_eq_mul,
      sub_mul, Finset.sum_sub_distrib]
    congr 1
    · simp [Finset.sum_ite_eq, mul_assoc]
    · refine Finset.sum_congr rfl fun j _ => ?_; ring
  rw [h1, h2]
  simp only [h3, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

end PositivityTheory.Rg.Sw.WR.G
