import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC

open scoped ComplexConjugate

namespace UpperTheory.V.Z.Sym.Unl

/- English proof (translation)
Establish `h1 : a * conj a = ((‖a‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[Complex.mul_conj']`. Use `push_cast`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem sq_of_conj {a x : ℂ} (h : conj a * x = a) :
    a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) * x := by
  have h1 : a * conj a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; push_cast; rfl
  calc a * a = a * (conj a * x) := by rw [h]
    _ = (a * conj a) * x := by ring
    _ = _ := by rw [h1]

/- English proof (translation)
Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hn : Complex.normSq z = p`. Establish `e` using `Complex.mul_conj z`. Rewrite `e` using `[hz]`. Conclude with `e.symm` after adjusting the coercions.

Establish `hre` using `congrArg Complex.re hzt`. Establish `him` using `congrArg Complex.im hzt`. Simplify using `[Complex.inv_re, Complex.inv_im, hn] at hre him`. Establish `hn2 : z.re * z.re + z.im * z.im = p` using `by rw [← hn, Complex.normSq_apply]`. Establish `hv : z.im = 0`.

Establish `e : z.im * (p - 1) = 0`. Establish `e2 : z.im * (p - 1) = p * (z.im + -z.im / p)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, him, mul_zero]`.

Break down `mul_eq_zero.mp e with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hre' : (z.re + 2) * p + z.re = t * p`.

Rewrite using `[← hre]`. Clear the denominators using the available nonvanishing facts. Establish `hu : (z.re - s) * (z.re + s) = 0`. Rewrite `hn2` using `[hv]`. Take the linear combination `hn2 - hs`.

Establish `hr : z.re = s`. Break down `mul_eq_zero.mp hu with h | h` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. It suffices to derive a contradiction. Establish `hm : z.re = -s` using `by linarith`.

Rewrite `hre'` using `[hm, ← hs]`. Establish `hs1 : 1 < s` using `by nlinarith`. Use polynomial arithmetic with `[mul_nonneg ht (mul_nonneg hs0.le hs0.le), mul_pos hs0 (mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hs1))]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[hr]`.

Simplify using `[hv]`.
-/
private theorem ratio_eq {p s t : ℝ} (hp : 2 ≤ p) (hs0 : 0 < s) (hs : s * s = p) {z : ℂ}
    (hz : z * conj z = (p : ℂ)) (ht : 0 ≤ t) (hzt : z + 2 + z⁻¹ = (t : ℂ)) : z = (s : ℂ) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hn : Complex.normSq z = p := by
    have e := Complex.mul_conj z
    rw [hz] at e
    exact_mod_cast e.symm
  have hre := congrArg Complex.re hzt
  have him := congrArg Complex.im hzt
  simp [Complex.inv_re, Complex.inv_im, hn] at hre him
  have hn2 : z.re * z.re + z.im * z.im = p := by rw [← hn, Complex.normSq_apply]
  have hv : z.im = 0 := by
    have e : z.im * (p - 1) = 0 := by
      have e2 : z.im * (p - 1) = p * (z.im + -z.im / p) := by
        field_simp
        ring
      rw [e2, him, mul_zero]
    rcases mul_eq_zero.mp e with h | h
    · exact h
    · exfalso
      linarith
  have hre' : (z.re + 2) * p + z.re = t * p := by
    rw [← hre]
    field_simp
  have hu : (z.re - s) * (z.re + s) = 0 := by
    rw [hv] at hn2
    linear_combination hn2 - hs
  have hr : z.re = s := by
    rcases mul_eq_zero.mp hu with h | h
    · linarith
    · exfalso
      have hm : z.re = -s := by linarith
      rw [hm, ← hs] at hre'
      have hs1 : 1 < s := by nlinarith
      nlinarith [mul_nonneg ht (mul_nonneg hs0.le hs0.le), mul_pos hs0 (mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hs1))]
  apply Complex.ext
  · simp [hr]
  · simp [hv]

/- English proof (translation)
Introduce `hab`. Establish `hx0 : x ≠ 0`. Introduce `h0`. Rewrite `hx` using `[h0, norm_zero]`. Conclude with `zero_ne_one hx`.

Establish `hσx0 : σ x ≠ 0`. Introduce `h0`. Rewrite `hσx` using `[h0, norm_zero]`. Conclude with `zero_ne_one hσx`. Establish `hpR : (2 : ℝ) ≤ p` using `by exact_mod_cast hp`.

Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hpC : (p : ℂ) ≠ 0` using `by exact_mod_cast (show p ≠ 0 by omega)`. Establish `hprod0 : α * β ≠ 0`. Rewrite using `[hprod]`. Conclude with `mul_ne_zero hx0 (pow_ne_zero _ hpC)`.

Establish `hβ : β ≠ 0` using `right_ne_zero_of_mul hprod0`. Establish `hα : α ≠ 0` using `left_ne_zero_of_mul hprod0`. Use `set s := Real.sqrt p with hs_def`. Establish `hs0 : 0 < s` using `Real.sqrt_pos.mpr hp0`. Establish `hss : s * s = p` using `Real.mul_self_sqrt hp0.le`.

Establish `hn : Complex.normSq α = p * Complex.normSq β`. Rewrite using `[← Complex.sq_norm, ← Complex.sq_norm]`. Conclude with `hab`. Establish `hnβ : (Complex.normSq β : ℂ) ≠ 0`. Conclude with `(Complex.normSq_pos.mpr hβ).ne'` after adjusting the coercions.

Establish `hz : (α / β) * conj (α / β) = ((p : ℝ) : ℂ)`. Rewrite using `[map_div₀, div_mul_div_comm, Complex.mul_conj, Complex.mul_conj, hn]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `key : α / β + 2 + (α / β)⁻¹ = (a * a) / (α * β)`.

Rewrite using `[← hsum, inv_div]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hzt : α / β + 2 + (α / β)⁻¹ = ((‖a‖ ^ 2 / (p : ℝ) ^ m : ℝ) : ℂ)`. Rewrite using `[key, sq_of_conj ha, hprod]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `ht : (0 : ℝ) ≤ ‖a‖ ^ 2 / (p : ℝ) ^ m` using `by positivity`. Establish `hz'` using `ratio_eq hpR hs0 hss hz ht hzt`. Establish `hαs : α = (s : ℂ) * β` using `(div_eq_iff hβ).mp hz'`.

Establish `k2 : (s : ℂ) * (a * a) = (1 + (s : ℂ)) ^ 2 * (x * (p : ℂ) ^ m)`. Rewrite using `[← hprod, ← hsum, hαs]`. Expand and normalize the polynomial expressions, which then agree. Establish `k3` using `congrArg σ k2`. Simplify using `only [map_mul, map_add, map_pow, map_natCast, map_one, hσ] at k3`.

Rewrite `k3` using `[sq_of_conj hσa]`. Move the coercions through the operations in `at k3`. Establish `k4 : (-(s * ‖σ a‖ ^ 2 : ℝ) : ℂ) * σ x = ((1 - s) ^ 2 * (p : ℝ) ^ m : ℝ) * σ x`. Use `push_cast`. Take the linear combination `k3`.

Establish `k5` using `mul_right_cancel₀ hσx0 k4`. Establish `k6 : -(s * ‖σ a‖ ^ 2) = (1 - s) ^ 2 * (p : ℝ) ^ m` using `by exact_mod_cast k5`. Establish `hs1 : 1 < s` using `by nlinarith`. Establish `hpm : 0 < (p : ℝ) ^ m` using `pow_pos hp0 m`. Use polynomial arithmetic with `[mul_nonneg hs0.le (sq_nonneg ‖σ a‖), mul_pos (pow_pos (sub_pos.mpr hs1) 2) hpm]`.
-/
private theorem abs_ratio_ne_of_sqrt_flip (p m : ℕ) (a x α β : ℂ) (σ : ℂ ≃+* ℂ) (hp : 2 ≤ p) (hx : ‖x‖ = 1)
    (hσx : ‖σ x‖ = 1) (hσ : σ ((Real.sqrt p : ℝ) : ℂ) = -((Real.sqrt p : ℝ) : ℂ))
    (ha : conj a * x = a) (hσa : conj (σ a) * σ x = σ a) (hsum : α + β = a)
    (hprod : α * β = x * (p : ℂ) ^ m) : ‖α‖ ^ 2 ≠ (p : ℝ) * ‖β‖ ^ 2 := by
  intro hab
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hx
    exact zero_ne_one hx
  have hσx0 : σ x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hσx
    exact zero_ne_one hσx
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hprod0 : α * β ≠ 0 := by
    rw [hprod]
    exact mul_ne_zero hx0 (pow_ne_zero _ hpC)
  have hβ : β ≠ 0 := right_ne_zero_of_mul hprod0
  have hα : α ≠ 0 := left_ne_zero_of_mul hprod0
  set s := Real.sqrt p with hs_def
  have hs0 : 0 < s := Real.sqrt_pos.mpr hp0
  have hss : s * s = p := Real.mul_self_sqrt hp0.le
  have hn : Complex.normSq α = p * Complex.normSq β := by
    rw [← Complex.sq_norm, ← Complex.sq_norm]
    exact hab
  have hnβ : (Complex.normSq β : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr hβ).ne'
  have hz : (α / β) * conj (α / β) = ((p : ℝ) : ℂ) := by
    rw [map_div₀, div_mul_div_comm, Complex.mul_conj, Complex.mul_conj, hn]
    push_cast
    field_simp
  have key : α / β + 2 + (α / β)⁻¹ = (a * a) / (α * β) := by
    rw [← hsum, inv_div]
    field_simp
    ring
  have hzt : α / β + 2 + (α / β)⁻¹ = ((‖a‖ ^ 2 / (p : ℝ) ^ m : ℝ) : ℂ) := by
    rw [key, sq_of_conj ha, hprod]
    push_cast
    field_simp
  have ht : (0 : ℝ) ≤ ‖a‖ ^ 2 / (p : ℝ) ^ m := by positivity
  have hz' := ratio_eq hpR hs0 hss hz ht hzt
  have hαs : α = (s : ℂ) * β := (div_eq_iff hβ).mp hz'
  have k2 : (s : ℂ) * (a * a) = (1 + (s : ℂ)) ^ 2 * (x * (p : ℂ) ^ m) := by
    rw [← hprod, ← hsum, hαs]
    ring
  have k3 := congrArg σ k2
  simp only [map_mul, map_add, map_pow, map_natCast, map_one, hσ] at k3
  rw [sq_of_conj hσa] at k3
  push_cast at k3
  have k4 : (-(s * ‖σ a‖ ^ 2 : ℝ) : ℂ) * σ x = ((1 - s) ^ 2 * (p : ℝ) ^ m : ℝ) * σ x := by
    push_cast
    linear_combination k3
  have k5 := mul_right_cancel₀ hσx0 k4
  have k6 : -(s * ‖σ a‖ ^ 2) = (1 - s) ^ 2 * (p : ℝ) ^ m := by exact_mod_cast k5
  have hs1 : 1 < s := by nlinarith
  have hpm : 0 < (p : ℝ) ^ m := pow_pos hp0 m
  nlinarith [mul_nonneg hs0.le (sq_nonneg ‖σ a‖), mul_pos (pow_pos (sub_pos.mpr hs1) 2) hpm]

end UpperTheory.V.Z.Sym.Unl

/- English proof (translation)
Introduce `p m a x α β σ hp hx hσx hσ ha hσa hsum hprod`. Conclude with `UpperTheory.V.Z.Sym.Unl.abs_ratio_ne_of_sqrt_flip p m a x α β σ hp hx hσx hσ ha hσa hsum hprod`.
-/
theorem UpperTheory.V.Z.Sym.Unl.halfAlg :
    UpperTheory.V.Z.Sym.Unl.HalfAlg := by
  intro p m a x α β σ hp hx hσx hσ ha hσa hsum hprod
  exact UpperTheory.V.Z.Sym.Unl.abs_ratio_ne_of_sqrt_flip p m a x α β σ hp hx hσx hσ ha hσa hsum hprod
