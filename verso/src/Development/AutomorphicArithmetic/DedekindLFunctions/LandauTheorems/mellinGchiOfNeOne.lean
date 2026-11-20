import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.MellinRamp

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Simplify using `at hs`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h`.

Rewrite `hs` using `[sub_eq_zero.mp h]`. Simplify using `at hs`.
-/
theorem mellin_Gchi_of_ne_one_ne {s : ℂ} (hs : 1 < s.re) : s ≠ 0 ∧ s - 1 ≠ 0 := by
  constructor
  · rintro rfl
    simp at hs
    linarith
  · intro h
    rw [sub_eq_zero.mp h] at hs
    simp at hs

/- English proof (translation)
Take `⟨h0, h1⟩` from `mellin_Gchi_of_ne_one_ne hs`. Apply `Integrable.of_integral_ne_zero` to reduce the goal to its premises. Rewrite using `[mellin_ramp n hn s hs]`. Establish `hnC : (n : ℂ) ≠ 0` using `by exact_mod_cast (by omega : n ≠ 0)`. Conclude with `div_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hnC)) (mul_ne_zero h0 h1)`.
-/
theorem mellin_Gchi_of_ne_one_int (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => ((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
  obtain ⟨h0, h1⟩ := mellin_Gchi_of_ne_one_ne hs
  apply Integrable.of_integral_ne_zero
  rw [mellin_ramp n hn s hs]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  exact div_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hnC)) (mul_ne_zero h0 h1)

/- English proof (translation)
Establish `h` using `mellin_ramp n hn (s.re : ℂ) (by simpa using hs)`. Apply `ofReal_injective` to reduce the goal to its premises. Rewrite using `[← integral_complex_ofReal, ofReal_div, ofReal_cpow (Nat.cast_nonneg n)]`. Use `push_cast`. Rewrite using `[← h]`.

Use `setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_` and prove the remaining obligations. Establish `hy0 : (0 : ℝ) < y` using `lt_trans one_pos hy`. Rewrite using `[norm_mul, norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real, Real.norm_of_nonneg (le_max_right _ _)]`. Express the relevant statement in the definitionally equal form `(((max (y / n - 1) 0 * y ^ (-s - 1).re : ℝ)) : ℂ) = _`. Rewrite using `[ofReal_mul, ofReal_cpow hy0.le]`.

Simplify using the standard rewrite rules.
-/
theorem mellin_Gchi_of_ne_one_norm (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), ‖((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)‖ =
      (n : ℝ) ^ (-s.re) / (s.re * (s.re - 1)) := by
  have h := mellin_ramp n hn (s.re : ℂ) (by simpa using hs)
  apply ofReal_injective
  rw [← integral_complex_ofReal, ofReal_div, ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real,
    Real.norm_of_nonneg (le_max_right _ _)]
  change (((max (y / n - 1) 0 * y ^ (-s - 1).re : ℝ)) : ℂ) = _
  rw [ofReal_mul, ofReal_cpow hy0.le]
  simp

/- English proof (translation)
Unfold `ramp`. Apply `hasSum_sum_of_ne_finset_zero` to reduce the goal to its premises. Introduce `n hn`. Establish `hn' : ⌊y⌋₊ + 1 ≤ n` using `by simpa using hn`. Establish `hpos : (0 : ℝ) < n`.

Establish `: 0 < n` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hlt : y < n`. Establish `h1` using `Nat.lt_floor_add_one y`. Establish `h2 : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ n` using `by exact_mod_cast hn'`.

Move the coercions through the operations in `at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: max (y / n - 1) 0 = 0`. Apply `max_eq_right` to reduce the goal to its premises. Use `(div_lt_one hpos).mpr hlt` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem mellin_Gchi_of_ne_one_hasSum (f : ℕ → ℂ) (y : ℝ) :
    HasSum (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * f n *
      ((max (y / n - 1) 0 : ℝ) : ℂ)) (ramp f y) := by
  unfold ramp
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  have hn' : ⌊y⌋₊ + 1 ≤ n := by simpa using hn
  have hpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hlt : y < n := by
    have h1 := Nat.lt_floor_add_one y
    have h2 : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn'
    push_cast at h2
    linarith
  have : max (y / n - 1) 0 = 0 := by
    apply max_eq_right
    have := (div_lt_one hpos).mpr hlt
    linarith
  rw [this]
  simp

/- English proof (translation)
Use `set a : ℕ → ℂ := fun n => f n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) with ha`. Set `F : ℕ → ℝ → ℂ` to `fun n y => match n with`. Consider the case `0 => g y`. Consider the case `m + 1 => a (m + 1) * (((max (y / ((m + 1 : ℕ) : ℝ) - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1))`. Establish `hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 1))`.

Introduce and unpack `(_ | m)`. Conclude with `hg`. Conclude with `(mellin_Gchi_of_ne_one_int (m + 1) (by omega) s hs).const_mul _`. Establish `hsum : Summable fun n => ∫ y in Ioi (1 : ℝ), ‖F n y‖`. Rewrite using `[← summable_nat_add_iff 1]`.

Establish `h1` using `((summable_nat_add_iff 1).mpr hf.norm).div_const (s.re * (s.re - 1))`. Use `h1.congr fun m => ?_` and prove the remaining obligations. Simplify using `only [F]`. Repeatedly rewrite using `[norm_mul (a (m + 1))]`. Rewrite using `[integral_const_mul, mellin_Gchi_of_ne_one_norm (m + 1) (by omega) s hs, LSeries.norm_term_eq, if_neg (by omega), Real.rpow_neg (Nat.cast_nonneg _)]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h` using `hasSum_integral_of_summable_integral_norm hint hsum`. Establish `hF : ∀ y, ∑' n, F n y = ramp f y * (y : ℂ) ^ (-s - 1) + g y`. Introduce `y`. Establish `h1` using `(hasSum_nat_add_iff' 1).mpr ((mellin_Gchi_of_ne_one_hasSum f y).mul_right ((y : ℂ) ^ (-s - 1)))`.

Establish `h2 : HasSum (fun n => F (n + 1) y) (ramp f y * (y : ℂ) ^ (-s - 1))`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression. Use extensionality with `m`. Simplify using `only [F, ha]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Establish `h3` using `(hasSum_nat_add_iff (f := fun n => F n y) 1).mp h2`. Simplify `h3.tsum_eq` using `[F]`. Rewrite `h` using `[hF]`.

Establish `h1` using `(hasSum_nat_add_iff' 1).mpr (hf.hasSum.div_const (s * (s - 1)))`. Establish `h2 : HasSum (fun n => ∫ y in Ioi (1 : ℝ), F (n + 1) y) (LSeries a s / (s * (s - 1)))`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression. Use extensionality with `m`.

Simplify using `only [F]`. Rewrite using `[integral_const_mul, mellin_ramp (m + 1) (by omega) s hs, LSeries.term_of_ne_zero (by omega), cpow_neg]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[LSeries]`. Establish `h3` using `(hasSum_nat_add_iff (f := fun n => ∫ y in Ioi (1 : ℝ), F n y) 1).mp h2`.

Simplify `h.unique h3` using `[F]`.
-/
theorem mellin_Gchi_of_ne_one_ramp (f : ℕ → ℂ) (s : ℂ) (hs : 1 < s.re)
    (hf : LSeriesSummable (fun n => f n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s)
    (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi 1)) :
    ∫ y in Ioi (1 : ℝ), (ramp f y * (y : ℂ) ^ (-s - 1) + g y) =
      LSeries (fun n => f n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s / (s * (s - 1)) +
        ∫ y in Ioi (1 : ℝ), g y := by
  set a : ℕ → ℂ := fun n => f n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) with ha
  let F : ℕ → ℝ → ℂ := fun n y => match n with
    | 0 => g y
    | m + 1 => a (m + 1) * (((max (y / ((m + 1 : ℕ) : ℝ) - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1))
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 1)) := by
    rintro (_ | m)
    · exact hg
    · exact (mellin_Gchi_of_ne_one_int (m + 1) (by omega) s hs).const_mul _
  have hsum : Summable fun n => ∫ y in Ioi (1 : ℝ), ‖F n y‖ := by
    rw [← summable_nat_add_iff 1]
    have h1 := ((summable_nat_add_iff 1).mpr hf.norm).div_const (s.re * (s.re - 1))
    refine h1.congr fun m => ?_
    simp only [F]
    simp_rw [norm_mul (a (m + 1))]
    rw [integral_const_mul, mellin_Gchi_of_ne_one_norm (m + 1) (by omega) s hs,
      LSeries.norm_term_eq, if_neg (by omega), Real.rpow_neg (Nat.cast_nonneg _)]
    ring
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hF : ∀ y, ∑' n, F n y = ramp f y * (y : ℂ) ^ (-s - 1) + g y := by
    intro y
    have h1 := (hasSum_nat_add_iff' 1).mpr
      ((mellin_Gchi_of_ne_one_hasSum f y).mul_right ((y : ℂ) ^ (-s - 1)))
    have h2 : HasSum (fun n => F (n + 1) y) (ramp f y * (y : ℂ) ^ (-s - 1)) := by
      convert h1 using 1
      · rfl
      · ext m
        simp only [F, ha]
        ring
      · simp
    have h3 := (hasSum_nat_add_iff (f := fun n => F n y) 1).mp h2
    simpa [F] using h3.tsum_eq
  simp_rw [hF] at h
  have h1 := (hasSum_nat_add_iff' 1).mpr (hf.hasSum.div_const (s * (s - 1)))
  have h2 : HasSum (fun n => ∫ y in Ioi (1 : ℝ), F (n + 1) y) (LSeries a s / (s * (s - 1))) := by
    convert h1 using 1
    · rfl
    · ext m
      simp only [F]
      rw [integral_const_mul, mellin_ramp (m + 1) (by omega) s hs,
        LSeries.term_of_ne_zero (by omega), cpow_neg]
      ring
    · simp [LSeries]
  have h3 := (hasSum_nat_add_iff (f := fun n => ∫ y in Ioi (1 : ℝ), F n y) 1).mp h2
  simpa [F] using h.unique h3

/- English proof (translation)
Take `⟨h0, h1⟩` from `mellin_Gchi_of_ne_one_ne hs`. Use `set c := deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 with hc`. Establish `ha : (-s).re < -1` using `by simp; linarith`. Establish `h` using `mellin_Gchi_of_ne_one_ramp (fun n => χ n) s hs (χ.LSeriesSummable_twist_vonMangoldt hs) (fun y => c * (y : ℂ) ^ (-s)) ((integrableOn_Ioi_cpow_of_lt ha one_pos).const_mul c)`. Establish `hL : LSeries (fun n : ℕ => χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s = _` using `χ.LSeries_twist_vonMangoldt_eq hs`.

Rewrite `h` using `[hL, ← χ.LFunction_eq_LSeries hs, ← χ.deriv_LFunction_eq_deriv_LSeries hs, integral_const_mul, integral_Ioi_cpow_of_lt ha one_pos]`. Rewrite using `[setIntegral_congr_fun measurableSet_Ioi (g := fun y : ℝ => ramp (fun n => χ n) y * (y : ℂ) ^ (-s - 1) + c * (y : ℂ) ^ (-s)), h]`. Establish `e2 : -s + 1 = -(s - 1)` using `by ring`. Rewrite using `[e2, neg_div (DirichletCharacter.LFunction χ s)]`. Generalize the expression as in `deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s = d`.

Simplify using `only [ofReal_one, one_cpow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Introduce `y hy`. Establish `hy0 : (y : ℂ) ≠ 0` using `by exact_mod_cast (lt_trans one_pos hy).ne'`.

Simplify using `only [Gchi, if_neg hχ, ← hc]`. Rewrite using `[cpow_sub _ _ hy0, cpow_one]`. Clear the denominators using the available nonvanishing facts.
-/
theorem mellin_Gchi_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), Gchi χ y * (y : ℂ) ^ (-s - 1) =
      -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          s * (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)) / (s * (s - 1)) := by
  obtain ⟨h0, h1⟩ := mellin_Gchi_of_ne_one_ne hs
  set c := deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 with hc
  have ha : (-s).re < -1 := by simp; linarith
  have h := mellin_Gchi_of_ne_one_ramp (fun n => χ n) s hs
    (χ.LSeriesSummable_twist_vonMangoldt hs) (fun y => c * (y : ℂ) ^ (-s))
    ((integrableOn_Ioi_cpow_of_lt ha one_pos).const_mul c)
  have hL : LSeries (fun n : ℕ => χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s = _ :=
    χ.LSeries_twist_vonMangoldt_eq hs
  rw [hL, ← χ.LFunction_eq_LSeries hs, ← χ.deriv_LFunction_eq_deriv_LSeries hs,
    integral_const_mul, integral_Ioi_cpow_of_lt ha one_pos] at h
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun y : ℝ =>
    ramp (fun n => χ n) y * (y : ℂ) ^ (-s - 1) + c * (y : ℂ) ^ (-s)), h]
  · have e2 : -s + 1 = -(s - 1) := by ring
    rw [e2, neg_div (DirichletCharacter.LFunction χ s)]
    generalize deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s = d
    simp only [ofReal_one, one_cpow]
    field_simp
    ring
  · intro y hy
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast (lt_trans one_pos hy).ne'
    simp only [Gchi, if_neg hχ, ← hc]
    rw [cpow_sub _ _ hy0, cpow_one]
    field_simp

end Deduction

end
