import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.MellinRamp

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.
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
Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem mellin_Gchi_of_ne_one_int (n : ℕ) (hn : 1 ≤ n) (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => ((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
  obtain ⟨h0, h1⟩ := mellin_Gchi_of_ne_one_ne hs
  apply Integrable.of_integral_ne_zero
  rw [mellin_ramp n hn s hs]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  exact div_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hnC)) (mul_ne_zero h0 h1)

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

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
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Introduce a local definition for the expression. Treat this case separately. Treat this case separately. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Both sides reduce to the same expression.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Rewrite the indicated hypotheses repeatedly using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Both sides reduce to the same expression. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
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
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the chosen expression with an arbitrary variable. Simplify using the standard rewrite rules.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
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
