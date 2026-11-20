import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.BridgeSt

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

/- English proof (translation)
Simplify using `using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x`.
-/
theorem hasDerivAt_line (x v : MC n) : HasDerivAt (fun t : ℂ => x + t • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x

/- English proof (translation)
Establish `hc : Continuous fun t : ℂ => (M0 + t • A).det` using `(continuous_const.add (continuous_id.smul continuous_const)).matrix_det`. Establish `: (fun t : ℂ => (M0 + t • A).det) 0 ≠ 0` using `by simpa using h`. Conclude with `hc.continuousAt.eventually_ne this`.
-/
theorem det_affine_eventually (M0 A : Matrix (Fin n) (Fin n) ℂ) (h : M0.det ≠ 0) :
    ∀ᶠ t : ℂ in 𝓝 0, (M0 + t • A).det ≠ 0 := by
  have hc : Continuous fun t : ℂ => (M0 + t • A).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have : (fun t : ℂ => (M0 + t • A).det) 0 ≠ 0 := by simpa using h
  exact hc.continuousAt.eventually_ne this

/- English proof (translation)
Use `set D : Matrix (Fin n) (Fin n) ℂ := fun a d => deriv (fun t : ℂ => (M0 + t • A)⁻¹ a d) 0 with hD`. Establish `hY : ∀ a d, HasDerivAt (fun t : ℂ => (M0 + t • A)⁻¹ a d) (D a d) 0` using `fun a d => (hdiff a d).hasDerivAt`. Establish `hid : ∀ i j, HasDerivAt (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) ((A * M0⁻¹ + M0 * D) i j) 0`. Introduce `i j`. Establish `e : (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) = fun t : ℂ => ∑ k, (M0 i k + t * A i k) * (M0 + t • A)⁻¹ k j`.

Use function extensionality and compare the values at `t`. Simplify using `[Matrix.mul_apply]`. Rewrite using `[e]`. Establish `hs : HasDerivAt (fun t : ℂ => ∑ k, (M0 i k + t * A i k) * (M0 + t • A)⁻¹ k j) (∑ k, (A i k * M0⁻¹ k j + M0 i k * D k j)) 0`. Apply `HasDerivAt.fun_sum` to reduce the goal to its premises.

Introduce `k _`. Establish `h1 : HasDerivAt (fun t : ℂ => M0 i k + t * A i k) (A i k) 0`. Simplify using `using ((hasDerivAt_id (0 : ℂ)).mul_const (A i k)).const_add (M0 i k)`. Simplify using `using h1.fun_mul (hY k j)`. Use `hs using 1` and compare the differences between its conclusion and the goal.

Simplify using `[Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]`. Establish `hconst : ∀ i j, HasDerivAt (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) 0 0`. Introduce `i j`. Establish `hev : (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) =ᶠ[𝓝 0] fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) i j` using `by filter_upwards [det_affine_eventually M0 A h] with t ht`. Rewrite using `[Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ht)]`.

Conclude with `(hasDerivAt_const (0 : ℂ) ((1 : Matrix (Fin n) (Fin n) ℂ) i j)).congr_of_eventuallyEq hev`. Establish `hzero : A * M0⁻¹ + M0 * D = 0`. Use extensionality with `i j`. Conclude with `(hid i j).unique (hconst i j)`. Establish `hDv : D = -(M0⁻¹ * A * M0⁻¹)`.

Establish `h1 : M0⁻¹ * M0 = 1` using `Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)`. Establish `h2 : M0 * D = -(A * M0⁻¹)` using `by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hzero`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hDv]`. Conclude with `hY a d`.
-/
theorem inv_line (M0 A : Matrix (Fin n) (Fin n) ℂ) (h : M0.det ≠ 0)
    (hdiff : ∀ a d, DifferentiableAt ℂ (fun t : ℂ => (M0 + t • A)⁻¹ a d) 0) (a d : Fin n) :
    HasDerivAt (fun t : ℂ => (M0 + t • A)⁻¹ a d) ((-(M0⁻¹ * A * M0⁻¹)) a d) 0 := by
  set D : Matrix (Fin n) (Fin n) ℂ := fun a d => deriv (fun t : ℂ => (M0 + t • A)⁻¹ a d) 0 with hD
  have hY : ∀ a d, HasDerivAt (fun t : ℂ => (M0 + t • A)⁻¹ a d) (D a d) 0 := fun a d => (hdiff a d).hasDerivAt

  have hid : ∀ i j, HasDerivAt (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) ((A * M0⁻¹ + M0 * D) i j) 0 := by
    intro i j
    have e : (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) =
        fun t : ℂ => ∑ k, (M0 i k + t * A i k) * (M0 + t • A)⁻¹ k j := by
      funext t; simp [Matrix.mul_apply]
    rw [e]
    have hs : HasDerivAt (fun t : ℂ => ∑ k, (M0 i k + t * A i k) * (M0 + t • A)⁻¹ k j)
        (∑ k, (A i k * M0⁻¹ k j + M0 i k * D k j)) 0 := by
      apply HasDerivAt.fun_sum
      intro k _
      have h1 : HasDerivAt (fun t : ℂ => M0 i k + t * A i k) (A i k) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (A i k)).const_add (M0 i k)
      simpa using h1.fun_mul (hY k j)
    convert hs using 1
    simp [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]
  have hconst : ∀ i j, HasDerivAt (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) 0 0 := by
    intro i j
    have hev : (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) =ᶠ[𝓝 0] fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
      filter_upwards [det_affine_eventually M0 A h] with t ht
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ht)]
    exact (hasDerivAt_const (0 : ℂ) ((1 : Matrix (Fin n) (Fin n) ℂ) i j)).congr_of_eventuallyEq hev
  have hzero : A * M0⁻¹ + M0 * D = 0 := by
    ext i j
    exact (hid i j).unique (hconst i j)
  have hDv : D = -(M0⁻¹ * A * M0⁻¹) := by
    have h1 : M0⁻¹ * M0 = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)
    have h2 : M0 * D = -(A * M0⁻¹) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hzero
    calc D = M0⁻¹ * M0 * D := by rw [h1, Matrix.one_mul]
      _ = M0⁻¹ * (M0 * D) := by rw [Matrix.mul_assoc]
      _ = -(M0⁻¹ * A * M0⁻¹) := by rw [h2, Matrix.mul_neg, Matrix.mul_assoc]
  rw [← hDv]
  exact hY a d

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mX (s : ℂ) (x v : MC n) (t : ℂ) :
    1 - (Complex.I * s) • Matrix.of (x + t • v) = (1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mY (s : ℂ) (x v : MC n) (t : ℂ) :
    1 + (Complex.I * s) • Matrix.of (x + t • v) = (1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Establish `hA` using `entAn_inv (entAn_X (Complex.I * s) x) h a d`. Establish `e : (fun t : ℂ => ((1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v))⁻¹ a d) = (fun B : MC n => (1 - (Complex.I * s) • Matrix.of B)⁻¹ a d) ∘ (fun t : ℂ => x + t • v)`. Use function extensionality and compare the values at `t`. Simplify using `only [Function.comp]`. Rewrite using `[mX s x v t]`.

Rewrite using `[e]`. Establish `hA' : DifferentiableAt ℂ (fun B : MC n => (1 - (Complex.I * s) • Matrix.of B)⁻¹ a d) ((fun t : ℂ => x + t • v) 0)`. Simplify using `using hA.differentiableAt`. Conclude with `hA'.comp (0 : ℂ) (hasDerivAt_line x v).differentiableAt`.
-/
theorem diff_inv_X (s : ℂ) (x v : MC n) (h : (1 - (Complex.I * s) • Matrix.of x).det ≠ 0) (a d : Fin n) :
    DifferentiableAt ℂ (fun t : ℂ => ((1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v))⁻¹ a d) 0 := by
  have hA := entAn_inv (entAn_X (Complex.I * s) x) h a d
  have e : (fun t : ℂ => ((1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v))⁻¹ a d) =
      (fun B : MC n => (1 - (Complex.I * s) • Matrix.of B)⁻¹ a d) ∘ (fun t : ℂ => x + t • v) := by
    funext t
    simp only [Function.comp]
    rw [mX s x v t]
  rw [e]
  have hA' : DifferentiableAt ℂ (fun B : MC n => (1 - (Complex.I * s) • Matrix.of B)⁻¹ a d) ((fun t : ℂ => x + t • v) 0) := by
    simpa using hA.differentiableAt
  exact hA'.comp (0 : ℂ) (hasDerivAt_line x v).differentiableAt

/- English proof (translation)
Establish `hA` using `entAn_inv (entAn_Y (Complex.I * s) x) h a d`. Establish `e : (fun t : ℂ => ((1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v))⁻¹ a d) = (fun B : MC n => (1 + (Complex.I * s) • Matrix.of B)⁻¹ a d) ∘ (fun t : ℂ => x + t • v)`. Use function extensionality and compare the values at `t`. Simplify using `only [Function.comp]`. Rewrite using `[mY s x v t]`.

Rewrite using `[e]`. Establish `hA' : DifferentiableAt ℂ (fun B : MC n => (1 + (Complex.I * s) • Matrix.of B)⁻¹ a d) ((fun t : ℂ => x + t • v) 0)`. Simplify using `using hA.differentiableAt`. Conclude with `hA'.comp (0 : ℂ) (hasDerivAt_line x v).differentiableAt`.
-/
theorem diff_inv_Y (s : ℂ) (x v : MC n) (h : (1 + (Complex.I * s) • Matrix.of x).det ≠ 0) (a d : Fin n) :
    DifferentiableAt ℂ (fun t : ℂ => ((1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v))⁻¹ a d) 0 := by
  have hA := entAn_inv (entAn_Y (Complex.I * s) x) h a d
  have e : (fun t : ℂ => ((1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v))⁻¹ a d) =
      (fun B : MC n => (1 + (Complex.I * s) • Matrix.of B)⁻¹ a d) ∘ (fun t : ℂ => x + t • v) := by
    funext t
    simp only [Function.comp]
    rw [mY s x v t]
  rw [e]
  have hA' : DifferentiableAt ℂ (fun B : MC n => (1 + (Complex.I * s) • Matrix.of B)⁻¹ a d) ((fun t : ℂ => x + t • v) 0) := by
    simpa using hA.differentiableAt
  exact hA'.comp (0 : ℂ) (hasDerivAt_line x v).differentiableAt

/- English proof (translation)
Introduce `n s x v h a d`. Establish `e : (fun t : ℂ => Ym s (x + t • v) a d) = fun t : ℂ => ((1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v))⁻¹ a d`. Use function extensionality and compare the values at `t`. Simplify using `only [Ym]`. Rewrite using `[mX s x v t]`.

Rewrite using `[e]`. Use `inv_line _ _ h (diff_inv_X s x v h) a d` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Ym, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_smul, Matrix.smul_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hYm : HYm := by
  intro n s x v h a d
  have e : (fun t : ℂ => Ym s (x + t • v) a d) =
      fun t : ℂ => ((1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v))⁻¹ a d := by
    funext t
    simp only [Ym]
    rw [mX s x v t]
  rw [e]
  have := inv_line _ _ h (diff_inv_X s x v h) a d
  convert this using 1
  simp only [Ym, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_smul, Matrix.smul_mul]
  ring

/- English proof (translation)
Introduce `n s x v h a d`. Establish `e : (fun t : ℂ => Yp s (x + t • v) a d) = fun t : ℂ => ((1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v))⁻¹ a d`. Use function extensionality and compare the values at `t`. Simplify using `only [Yp]`. Rewrite using `[mY s x v t]`.

Rewrite using `[e]`. Use `inv_line _ _ h (diff_inv_Y s x v h) a d` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Yp, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_smul, Matrix.smul_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hYp : HYp := by
  intro n s x v h a d
  have e : (fun t : ℂ => Yp s (x + t • v) a d) =
      fun t : ℂ => ((1 + (Complex.I * s) • Matrix.of x) + t • ((Complex.I * s) • Matrix.of v))⁻¹ a d := by
    funext t
    simp only [Yp]
    rw [mY s x v t]
  rw [e]
  have := inv_line _ _ h (diff_inv_Y s x v h) a d
  convert this using 1
  simp only [Yp, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_smul, Matrix.smul_mul]
  ring

end PositivityTheory.Rg.Sw.SP
