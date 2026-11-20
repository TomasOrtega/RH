import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Af.Rs.lBd :
    UpperTheory.V.Af.Rs.LBd := by
  intro L _ ψ s hs
  set f : ℕ → ℂ := fun n => ψ n / ((n : ℝ) ^ (2 * s) : ℝ) with hf
  set g : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 with hg
  have hs2 : (2 * s) ≠ 0 := by linarith
  have hbd : ∀ n, ‖f n‖ ≤ g n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hf, hg, Real.zero_rpow hs2]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hpos : (0 : ℝ) < (n : ℝ) ^ (2 * s) := Real.rpow_pos_of_pos (by linarith) _
      have hle : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ (2 * s) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      rw [Real.rpow_two] at hle
      simp only [hf, hg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      calc ‖ψ n‖ / (n : ℝ) ^ (2 * s) ≤ 1 / (n : ℝ) ^ (2 * s) :=
            div_le_div_of_nonneg_right (DirichletCharacter.norm_le_one ψ _) hpos.le
        _ ≤ 1 / (n : ℝ) ^ 2 := one_div_le_one_div_of_le (by positivity) hle
  have hgs : HasSum g (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have hsum : Summable f := Summable.of_norm_bounded hgs.summable hbd
  refine ⟨hsum, ?_⟩
  have hg2 : HasSum (fun n => g (n + 2)) (Real.pi ^ 2 / 6 - 1) := by
    have := (hasSum_nat_add_iff' (f := g) 2).mpr hgs
    simpa [Finset.sum_range_succ, hg] using this
  have htail : ‖∑' n, f (n + 2)‖ ≤ Real.pi ^ 2 / 6 - 1 :=
    tsum_of_norm_bounded hg2 (fun n => hbd (n + 2))
  have hsplit : UpperTheory.V.Af.Rs.Lps ψ s = 1 + ∑' n, f (n + 2) := by
    rw [UpperTheory.V.Af.Rs.Lps, ← hsum.sum_add_tsum_nat_add 2]
    simp [Finset.sum_range_succ, hf, Real.zero_rpow hs2]
  have hpi : Real.pi ^ 2 / 6 - 1 ≤ 3 / 4 := by
    have h1 := Real.pi_lt_d2
    have h0 := Real.pi_pos
    nlinarith
  rw [hsplit]
  constructor
  · have := norm_sub_norm_le (1 : ℂ) (-(∑' n, f (n + 2)))
    rw [sub_neg_eq_add, norm_neg, norm_one] at this
    linarith
  · have := norm_add_le (1 : ℂ) (∑' n, f (n + 2))
    rw [norm_one] at this
    linarith
