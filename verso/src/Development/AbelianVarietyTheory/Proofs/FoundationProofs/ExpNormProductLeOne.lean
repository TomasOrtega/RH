import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
namespace GlobalTheory.EisM

/- English proof (translation)
Establish `hs : ∀ i j, HasSum (fun n : ℕ => (z i * conj (z j) * T) ^ n / n) (-Complex.log (1 - z i * conj (z j) * T))` using `fun i j => Complex.hasSum_taylorSeries_neg_log (h i j)`. Establish `H` using `hasSum_sum (s := Finset.univ) (fun i _ => hasSum_sum (s := Finset.univ) (fun j _ => hs i j))`. Establish `H2` using `((Complex.hasSum_iff _ _).mp H).1`. Establish `hterm : ∀ n : ℕ, (∑ i, ∑ j, (z i * conj (z j) * T) ^ n / (n : ℂ)).re = T ^ n * ‖∑ i, z i ^ n‖ ^ 2 / n`. Introduce `n`.

Establish `e : (∑ i, ∑ j, (z i * conj (z j) * T) ^ n / (n : ℂ)) = (((T ^ n * ‖∑ i, z i ^ n‖ ^ 2 / n : ℝ)) : ℂ)`. Establish `e1 : ∀ i j, (z i * conj (z j) * T) ^ n / (n : ℂ) = z i ^ n * conj (z j ^ n) * ((T : ℂ) ^ n / n)`. Introduce `i j`. Rewrite using `[map_pow]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[e1]`. Establish `e2 : ∑ i, ∑ j, z i ^ n * conj (z j ^ n) * ((T : ℂ) ^ n / n) = (∑ i, z i ^ n) * conj (∑ j, z j ^ n) * ((T : ℂ) ^ n / n)`. Rewrite using `[map_sum, Finset.sum_mul_sum, Finset.sum_mul]`. Repeatedly rewrite using `[Finset.sum_mul]`. Rewrite using `[e2, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, Complex.ofReal_re]`. Establish `hre : (∑ i, ∑ j, -Complex.log (1 - z i * conj (z j) * T)).re = - ∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖`. Simplify using `[Complex.re_sum, Complex.log_re]`.

Rewrite `H2` using `[hre]`. Rewrite `H2` using `[hterm]`. Use `le_hasSum H2 1 (fun n _ => by positivity)` as an intermediate fact. Simplify using `using this`.
-/
theorem locineq_log_sum {ι : Type*} [Fintype ι] (z : ι → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (h : ∀ i j, ‖z i * conj (z j) * T‖ < 1) :
    T * ‖∑ i, z i‖ ^ 2 ≤ - ∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖ := by
  have hs : ∀ i j, HasSum (fun n : ℕ => (z i * conj (z j) * T) ^ n / n)
      (-Complex.log (1 - z i * conj (z j) * T)) := fun i j =>
    Complex.hasSum_taylorSeries_neg_log (h i j)
  have H := hasSum_sum (s := Finset.univ) (fun i _ => hasSum_sum (s := Finset.univ) (fun j _ => hs i j))
  have H2 := ((Complex.hasSum_iff _ _).mp H).1
  have hterm : ∀ n : ℕ, (∑ i, ∑ j, (z i * conj (z j) * T) ^ n / (n : ℂ)).re
      = T ^ n * ‖∑ i, z i ^ n‖ ^ 2 / n := by
    intro n
    have e : (∑ i, ∑ j, (z i * conj (z j) * T) ^ n / (n : ℂ))
        = (((T ^ n * ‖∑ i, z i ^ n‖ ^ 2 / n : ℝ)) : ℂ) := by
      have e1 : ∀ i j, (z i * conj (z j) * T) ^ n / (n : ℂ)
          = z i ^ n * conj (z j ^ n) * ((T : ℂ) ^ n / n) := by
        intro i j; rw [map_pow]; ring
      simp_rw [e1]
      have e2 : ∑ i, ∑ j, z i ^ n * conj (z j ^ n) * ((T : ℂ) ^ n / n)
          = (∑ i, z i ^ n) * conj (∑ j, z j ^ n) * ((T : ℂ) ^ n / n) := by
        rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
        simp_rw [Finset.sum_mul]
      rw [e2, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    rw [e, Complex.ofReal_re]
  have hre : (∑ i, ∑ j, -Complex.log (1 - z i * conj (z j) * T)).re
      = - ∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖ := by
    simp [Complex.re_sum, Complex.log_re]
  rw [hre] at H2
  simp_rw [hterm] at H2
  have := le_hasSum H2 1 (fun n _ => by positivity)
  simpa using this

/- English proof (translation)
Establish `hpos : ∀ i j, 0 < ‖1 - z i * conj (z j) * T‖`. Introduce `i j`. Use `norm_pos_iff.mpr (sub_ne_zero.mpr fun e => ?_)` and prove the remaining obligations. Use `h i j` as an intermediate fact. Rewrite `this` using `[← e, norm_one]`.

Conclude with `lt_irrefl _ this`. Establish `hP : ∏ i, ∏ j, ‖1 - z i * conj (z j) * T‖ = Real.exp (∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖)`. Rewrite using `[Real.exp_sum]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Real.exp_sum]`.

Conclude with `Finset.prod_congr rfl fun j _ => (Real.exp_log (hpos i j)).symm`. Rewrite using `[hP, ← Real.exp_add, Real.exp_le_one_iff]`. Use `locineq_log_sum z T hT h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem locineq_exp_prod {ι : Type*} [Fintype ι] (z : ι → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (h : ∀ i j, ‖z i * conj (z j) * T‖ < 1) :
    Real.exp (‖∑ i, z i‖ ^ 2 * T) * ∏ i, ∏ j, ‖1 - z i * conj (z j) * T‖ ≤ 1 := by
  have hpos : ∀ i j, 0 < ‖1 - z i * conj (z j) * T‖ := by
    intro i j
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun e => ?_)
    have := h i j
    rw [← e, norm_one] at this
    exact lt_irrefl _ this
  have hP : ∏ i, ∏ j, ‖1 - z i * conj (z j) * T‖
      = Real.exp (∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => (Real.exp_log (hpos i j)).symm
  rw [hP, ← Real.exp_add, Real.exp_le_one_iff]
  have := locineq_log_sum z T hT h
  linarith

/- English proof (translation)
Introduce `x y T hT0 hT1 hx hy`. Establish `hxT : ‖x‖ * T < 1`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Use polynomial arithmetic with `[norm_nonneg x, mul_le_mul_of_nonneg_left hT1.le (mul_nonneg (norm_nonneg x) (norm_nonneg x))]`.

Establish `hyT : ‖y‖ * T < 1`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Use polynomial arithmetic with `[norm_nonneg y, mul_le_mul_of_nonneg_left hT1.le (mul_nonneg (norm_nonneg y) (norm_nonneg y))]`. Establish `hxy : ‖x‖ * ‖y‖ * T < 1`.

Use polynomial arithmetic with `[mul_nonneg (sq_nonneg (‖x‖ - ‖y‖)) hT0]`. Set `z : Fin 3 → ℂ` to `![1, x, y]`. Establish `hnT : ‖(T : ℂ)‖ = T` using `by rw [Complex.norm_real, Real.norm_of_nonneg hT0]`. Establish `h : ∀ i j, ‖z i * conj (z j) * T‖ < 1`. Introduce `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [z, hnT, Complex.norm_conj, abs_of_nonneg hT0] <;> nlinarith`. Establish `key` using `locineq_exp_prod z T hT0 h`. Establish `c1 : ‖1 - conj x * T‖ = ‖1 - x * T‖`. Rewrite using `[← Complex.norm_conj (1 - x * T)]`.

Simplify using the standard rewrite rules. Establish `c2 : ‖1 - conj y * T‖ = ‖1 - y * T‖`. Rewrite using `[← Complex.norm_conj (1 - y * T)]`. Simplify using the standard rewrite rules. Establish `c3 : ‖1 - y * conj x * T‖ = ‖1 - x * conj y * T‖`.

Rewrite using `[← Complex.norm_conj (1 - x * conj y * T)]`. Simplify using the standard rewrite rules. Put the polynomial expressions in normal form. Establish `d0 : ‖1 - (T : ℂ)‖ = 1 - T`. Rewrite using `[← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]`.

Establish `dx : ‖1 - x * conj x * T‖ = 1 - ‖x‖ ^ 2 * T`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]`. Establish `dy : ‖1 - y * conj y * T‖ = 1 - ‖y‖ ^ 2 * T`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]`. Simplify using `only [z, Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_one, one_mul, mul_one] at key`.

Rewrite `key` using `[c1, c2, c3, d0, dx, dy]`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem locineq : ∀ (x y : ℂ) (T : ℝ), 0 ≤ T → T < 1 → ‖x‖ ^ 2 * T < 1 → ‖y‖ ^ 2 * T < 1 →
    Real.exp (‖1 + x + y‖ ^ 2 * T) * ((1 - T) * ‖(1 - x * T) * (1 - y * T)‖ ^ 2 *
      ((1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2)) ≤ 1 := by
  intro x y T hT0 hT1 hx hy
  have hxT : ‖x‖ * T < 1 := by
    by_contra hc; push_neg at hc
    nlinarith [norm_nonneg x, mul_le_mul_of_nonneg_left hT1.le (mul_nonneg (norm_nonneg x) (norm_nonneg x))]
  have hyT : ‖y‖ * T < 1 := by
    by_contra hc; push_neg at hc
    nlinarith [norm_nonneg y, mul_le_mul_of_nonneg_left hT1.le (mul_nonneg (norm_nonneg y) (norm_nonneg y))]
  have hxy : ‖x‖ * ‖y‖ * T < 1 := by
    nlinarith [mul_nonneg (sq_nonneg (‖x‖ - ‖y‖)) hT0]
  let z : Fin 3 → ℂ := ![1, x, y]
  have hnT : ‖(T : ℂ)‖ = T := by rw [Complex.norm_real, Real.norm_of_nonneg hT0]
  have h : ∀ i j, ‖z i * conj (z j) * T‖ < 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [z, hnT, Complex.norm_conj, abs_of_nonneg hT0] <;> nlinarith
  have key := locineq_exp_prod z T hT0 h
  have c1 : ‖1 - conj x * T‖ = ‖1 - x * T‖ := by
    rw [← Complex.norm_conj (1 - x * T)]; simp
  have c2 : ‖1 - conj y * T‖ = ‖1 - y * T‖ := by
    rw [← Complex.norm_conj (1 - y * T)]; simp
  have c3 : ‖1 - y * conj x * T‖ = ‖1 - x * conj y * T‖ := by
    rw [← Complex.norm_conj (1 - x * conj y * T)]; simp; ring_nf
  have d0 : ‖1 - (T : ℂ)‖ = 1 - T := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have dx : ‖1 - x * conj x * T‖ = 1 - ‖x‖ ^ 2 * T := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have dy : ‖1 - y * conj y * T‖ = 1 - ‖y‖ ^ 2 * T := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  simp only [z, Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_one, one_mul, mul_one] at key
  rw [c1, c2, c3, d0, dx, dy] at key
  rw [norm_mul]
  calc _ = Real.exp (‖1 + x + y‖ ^ 2 * T) * ((1 - T) * ‖1 - x * T‖ * ‖1 - y * T‖ *
        (‖1 - x * T‖ * (1 - ‖x‖ ^ 2 * T) * ‖1 - x * conj y * T‖) *
        (‖1 - y * T‖ * ‖1 - x * conj y * T‖ * (1 - ‖y‖ ^ 2 * T))) := by ring
    _ ≤ 1 := key

end GlobalTheory.EisM
