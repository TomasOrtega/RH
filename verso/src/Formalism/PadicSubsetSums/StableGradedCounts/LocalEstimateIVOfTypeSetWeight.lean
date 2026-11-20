import Formalism.PadicSubsetSums.CentralIdempotents.EigenbasisOfDistinctRoots
import Formalism.PadicSubsetSums.StableGradedCounts.PropositionOneCentralCount
import Formalism.PadicSubsetSums.StableGradedCounts.IRRDivisorDegreeSubSum
import Formalism.PadicSubsetSums.StableGradedCounts.IRRCycleProbSum
import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeRecipSum
import Formalism.PadicSubsetSums.StableGradedCounts.IRRLemmaLWeight
import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeToPartEqIff
import Formalism.PadicSubsetSums.StableGradedCounts.IRRPrimeToPartSpec
import Formalism.PadicSubsetSums.StableGradedCounts.IRRLemmaP
import Formalism.GaloisIrreducibility.NoSolvableTransitive
import Formalism.PadicSubsetSums.StableGradedCounts.IRRCentralIdemSelfAdjoint
import Formalism.PadicSubsetSums.StableGradedCounts.IRRIrredCountUpper
import Formalism.PadicSubsetSums.StableGradedCounts.IRRSquarefreeCount
import Formalism.PadicSubsetSums.StableGradedCounts.IRRTypeCountExact
import Formalism.PadicSubsetSums.StableGradedCounts.IRRCycleTypeProb

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `N Y hN hY`. Establish `hN' : (1 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `ht : 1 ≤ Y ^ ((3 : ℝ) / 4)` using `Real.one_le_rpow hY (by norm_num)`. Generalize the expression as in `Y ^ ((3 : ℝ) / 4) = t at ht ⊢`. Establish `hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2` using `by nlinarith`.

Establish `h1 : (3 * N + 1 : ℝ) ≤ 4 * N` using `by linarith`. Establish `h2 : 1 + 2 * (N : ℝ) ^ 2 * (t + 1) ≤ 5 * (N : ℝ) ^ 2 * t` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem excluded_set_simplification : ExcludedSimplify := by
  intro N Y hN hY
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : 1 ≤ Y ^ ((3 : ℝ) / 4) := Real.one_le_rpow hY (by norm_num)
  generalize Y ^ ((3 : ℝ) / 4) = t at ht ⊢
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have h1 : (3 * N + 1 : ℝ) ≤ 4 * N := by linarith
  have h2 : 1 + 2 * (N : ℝ) ^ 2 * (t + 1) ≤ 5 * (N : ℝ) ^ 2 * t := by nlinarith
  calc (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * (t + 1)) ≤ (4 * N) * (5 * (N : ℝ) ^ 2 * t) :=
        mul_le_mul h1 h2 (by nlinarith) (by linarith)
    _ = 20 * (N : ℝ) ^ 3 * t := by ring

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `c d Q m X N hc hd1 hdc hQ0 hQc hm0 hmc hN hX hmain`. Establish `hc1 : (1 : ℝ) ≤ c` using `by linarith`. Establish `hc0 : (0 : ℝ) < c` using `by linarith`. Establish `hd0 : (0 : ℝ) ≤ d` using `by linarith`. Establish `hA : c ^ 500 ≤ (X * c ^ (-20 : ℤ)) ^ ((1 : ℝ) / 4)`.

Establish `h1 : (1 : ℝ) ≤ (N : ℝ) ^ 4` using `one_le_pow₀ (by exact_mod_cast hN)`. Combine the equalities or inequalities in the displayed calculation. Establish `hXc : 0 ≤ X * c ^ (-20 : ℤ)` using `mul_nonneg hX.le (zpow_nonneg hc0.le _)`. Establish `hB : c ^ 2000 ≤ X * c ^ (-20 : ℤ)`. Establish `h4` using `pow_le_pow_left₀ (by positivity) hA 4`.

Establish `e1 : ((X * c ^ (-20 : ℤ)) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = X * c ^ (-20 : ℤ)`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hXc]`. Evaluate the numerical expressions. Rewrite `h4` using `[e1, ← pow_mul]`. Conclude with `h4`.

Establish `hC : c ^ 2020 ≤ X`. Establish `e2 : X * c ^ (-20 : ℤ) * c ^ (20 : ℕ) = X`. Rewrite using `[mul_assoc, ← zpow_natCast, ← zpow_add₀ hc0.ne']`. Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation.

Establish `t1 : d ^ 694 * Q ^ 521 ≤ c ^ 1736`. Establish `a1 : d ^ 694 ≤ c ^ 694` using `pow_le_pow_left₀ hd0 hdc _`. Establish `a2 : Q ^ 521 ≤ (c ^ 2) ^ 521` using `pow_le_pow_left₀ hQ0 hQc _`. Combine the equalities or inequalities in the displayed calculation. Establish `t2 : d ^ 232 * Q ^ 367 * (2 : ℝ) ^ (290 * 2) ≤ c ^ 1256`.

Establish `a1 : d ^ 232 ≤ c ^ 232` using `pow_le_pow_left₀ hd0 hdc _`. Establish `a2 : Q ^ 367 ≤ (c ^ 2) ^ 367` using `pow_le_pow_left₀ hQ0 hQc _`. Establish `a3 : (2 : ℝ) ^ (290 * 2) ≤ c ^ 290`. Rewrite using `[pow_mul']`. Conclude with `pow_le_pow_left₀ (by norm_num) (by norm_num; linarith) _`.

Combine the equalities or inequalities in the displayed calculation. Establish `t3 : (d * Q * (2 : ℝ) ^ 2) ^ ((1 : ℝ) / 1000) * m ≤ 2 * c ^ 6`. Establish `hb0 : 0 ≤ d * Q * (2 : ℝ) ^ 2` using `mul_nonneg (mul_nonneg hd0 hQ0) (by norm_num)`. Establish `hr : (d * Q * (2 : ℝ) ^ 2) ^ ((1 : ℝ) / 1000) ≤ 1 + d * Q * (2 : ℝ) ^ 2`. Break down `le_or_gt (d * Q * (2 : ℝ) ^ 2) 1 with h | h` into its components or cases.

Use `Real.rpow_le_one hb0 h (by norm_num : (0 : ℝ) ≤ 1 / 1000)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `Real.rpow_le_rpow_of_exponent_le h.le (by norm_num : (1 : ℝ) / 1000 ≤ 1)` as an intermediate fact. Rewrite `this` using `[Real.rpow_one]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hq : d * Q * (2 : ℝ) ^ 2 ≤ c ^ 4`. Establish `h1 : d * Q ≤ c * c ^ 2` using `mul_le_mul hdc hQc hQ0 hc0.le`. Use polynomial arithmetic with `[mul_nonneg (pow_nonneg hc0.le 3) (by linarith : (0 : ℝ) ≤ c - 4)]`. Establish `h4 : (1 : ℝ) ≤ c ^ 4` using `one_le_pow₀ hc1`. Combine the equalities or inequalities in the displayed calculation.

Establish `f1 : c ^ 1256 ≤ c ^ 1736` using `pow_le_pow_right₀ hc1 (by norm_num)`. Establish `f2 : c ^ 6 ≤ c ^ 1736` using `pow_le_pow_right₀ hc1 (by norm_num)`. Establish `f3 : 4 * c ^ 1736 ≤ c ^ 2020`. Establish `h5 : (4 : ℝ) ≤ c ^ 284` using `le_trans hc (le_self_pow₀ hc1 (by norm_num))`. Combine the equalities or inequalities in the displayed calculation.

Establish `s1 : c ^ 1736 + c ^ 1256 + 2 * c ^ 6 ≤ 4 * c ^ 1736` using `by linarith`. Conclude with `le_trans (add_le_add (add_le_add t1 t2) t3) (le_trans s1 (le_trans f3 hC))`.
-/
theorem q_p_threshold_bound : QPThreshold := by
  intro c d Q m X N hc hd1 hdc hQ0 hQc hm0 hmc hN hX hmain
  have hc1 : (1 : ℝ) ≤ c := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hd0 : (0 : ℝ) ≤ d := by linarith
  have hA : c ^ 500 ≤ (X * c ^ (-20 : ℤ)) ^ ((1 : ℝ) / 4) := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hN)
    calc c ^ 500 = 1 * c ^ 500 := (one_mul _).symm
      _ ≤ (N : ℝ) ^ 4 * c ^ 500 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ _ := hmain
  have hXc : 0 ≤ X * c ^ (-20 : ℤ) := mul_nonneg hX.le (zpow_nonneg hc0.le _)
  have hB : c ^ 2000 ≤ X * c ^ (-20 : ℤ) := by
    have h4 := pow_le_pow_left₀ (by positivity) hA 4
    have e1 : ((X * c ^ (-20 : ℤ)) ^ ((1 : ℝ) / 4)) ^ (4 : ℕ) = X * c ^ (-20 : ℤ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hXc]
      norm_num
    rw [e1, ← pow_mul] at h4
    exact h4
  have hC : c ^ 2020 ≤ X := by
    have e2 : X * c ^ (-20 : ℤ) * c ^ (20 : ℕ) = X := by
      rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hc0.ne']
      norm_num
    calc c ^ 2020 = c ^ 2000 * c ^ 20 := by ring
      _ ≤ X * c ^ (-20 : ℤ) * c ^ 20 := mul_le_mul_of_nonneg_right hB (by positivity)
      _ = X := e2
  have t1 : d ^ 694 * Q ^ 521 ≤ c ^ 1736 := by
    have a1 : d ^ 694 ≤ c ^ 694 := pow_le_pow_left₀ hd0 hdc _
    have a2 : Q ^ 521 ≤ (c ^ 2) ^ 521 := pow_le_pow_left₀ hQ0 hQc _
    calc d ^ 694 * Q ^ 521 ≤ c ^ 694 * (c ^ 2) ^ 521 :=
          mul_le_mul a1 a2 (pow_nonneg hQ0 _) (by positivity)
      _ = c ^ 1736 := by ring
  have t2 : d ^ 232 * Q ^ 367 * (2 : ℝ) ^ (290 * 2) ≤ c ^ 1256 := by
    have a1 : d ^ 232 ≤ c ^ 232 := pow_le_pow_left₀ hd0 hdc _
    have a2 : Q ^ 367 ≤ (c ^ 2) ^ 367 := pow_le_pow_left₀ hQ0 hQc _
    have a3 : (2 : ℝ) ^ (290 * 2) ≤ c ^ 290 := by
      rw [pow_mul']
      exact pow_le_pow_left₀ (by norm_num) (by norm_num; linarith) _
    calc d ^ 232 * Q ^ 367 * (2 : ℝ) ^ (290 * 2) ≤ c ^ 232 * (c ^ 2) ^ 367 * c ^ 290 :=
          mul_le_mul (mul_le_mul a1 a2 (pow_nonneg hQ0 _) (by positivity)) a3 (by positivity)
            (by positivity)
      _ = c ^ 1256 := by ring
  have t3 : (d * Q * (2 : ℝ) ^ 2) ^ ((1 : ℝ) / 1000) * m ≤ 2 * c ^ 6 := by
    have hb0 : 0 ≤ d * Q * (2 : ℝ) ^ 2 := mul_nonneg (mul_nonneg hd0 hQ0) (by norm_num)
    have hr : (d * Q * (2 : ℝ) ^ 2) ^ ((1 : ℝ) / 1000) ≤ 1 + d * Q * (2 : ℝ) ^ 2 := by
      rcases le_or_gt (d * Q * (2 : ℝ) ^ 2) 1 with h | h
      · have := Real.rpow_le_one hb0 h (by norm_num : (0 : ℝ) ≤ 1 / 1000)
        linarith
      · have := Real.rpow_le_rpow_of_exponent_le h.le (by norm_num : (1 : ℝ) / 1000 ≤ 1)
        rw [Real.rpow_one] at this
        linarith
    have hq : d * Q * (2 : ℝ) ^ 2 ≤ c ^ 4 := by
      have h1 : d * Q ≤ c * c ^ 2 := mul_le_mul hdc hQc hQ0 hc0.le
      nlinarith [mul_nonneg (pow_nonneg hc0.le 3) (by linarith : (0 : ℝ) ≤ c - 4)]
    have h4 : (1 : ℝ) ≤ c ^ 4 := one_le_pow₀ hc1
    calc (d * Q * (2 : ℝ) ^ 2) ^ ((1 : ℝ) / 1000) * m ≤ (1 + c ^ 4) * c ^ 2 :=
          mul_le_mul (by linarith) hmc hm0 (by positivity)
      _ ≤ 2 * c ^ 6 := by nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg c)]
  have f1 : c ^ 1256 ≤ c ^ 1736 := pow_le_pow_right₀ hc1 (by norm_num)
  have f2 : c ^ 6 ≤ c ^ 1736 := pow_le_pow_right₀ hc1 (by norm_num)
  have f3 : 4 * c ^ 1736 ≤ c ^ 2020 := by
    have h5 : (4 : ℝ) ≤ c ^ 284 := le_trans hc (le_self_pow₀ hc1 (by norm_num))
    calc 4 * c ^ 1736 ≤ c ^ 284 * c ^ 1736 := mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = c ^ 2020 := by ring
  have s1 : c ^ 1736 + c ^ 1256 + 2 * c ^ 6 ≤ 4 * c ^ 1736 := by linarith
  exact le_trans (add_le_add (add_le_add t1 t2) t3) (le_trans s1 (le_trans f3 hC))

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `c₀ c X B h P A hc₀ hc hX hlog hB hBc hh hhc hP hPA`. Establish `hlogpos : 0 < Real.log X` using `Real.log_pos hX`. Establish `hcpos : 0 < c` using `lt_of_lt_of_le hlogpos hlog`. Establish `hX0 : 0 < X` using `by linarith`. Establish `hc0c : (2 : ℝ) ^ 14 ≤ c₀ * c`.

Rewrite `hc` using `[div_le_iff₀ hc₀]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB5 : B ^ 5 ≤ 1024 * c ^ 15`. Combine the equalities or inequalities in the displayed calculation. Establish `hden : h * Real.log X ≤ c ^ 4`.

Combine the equalities or inequalities in the displayed calculation. Establish `hB0 : 0 < B ^ 5` using `pow_pos hB 5`. Establish `hD0 : 0 < h * Real.log X` using `mul_pos hh hlogpos`. Establish `hP' : c₀ * X / (1024 * c ^ 19) ≤ P`. Use `le_trans ?_ hP` and prove the remaining obligations.

Establish `e : c₀ * B ^ (-5 : ℤ) * X / (h * Real.log X) = c₀ * X / (B ^ 5 * (h * Real.log X))`. Rewrite using `[zpow_neg, zpow_ofNat]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, div_le_div_iff₀ (mul_pos (by norm_num) (pow_pos hcpos 19)) (mul_pos hB0 hD0)]`. Establish `h1 : B ^ 5 * (h * Real.log X) ≤ 1024 * c ^ 19`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `mul_le_mul_of_nonneg_left h1 (mul_pos hc₀ hX0).le`. Establish `hA : 8 * c ^ (-20 : ℤ) * X ≤ c₀ * X / (2048 * c ^ 19)`. Establish `e : 8 * c ^ (-20 : ℤ) * X = 8 * X / c ^ 20`. Rewrite using `[zpow_neg, zpow_ofNat]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, div_le_div_iff₀ (pow_pos hcpos 20) (mul_pos (by norm_num) (pow_pos hcpos 19))]`. Use polynomial arithmetic with `[mul_nonneg (mul_pos hX0 (pow_pos hcpos 19)).le (sub_nonneg.mpr hc0c)]`. Establish `e2 : c₀ * X / (2048 * c ^ 19) = (c₀ * X / (1024 * c ^ 19)) / 2` using `by ring`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem admissible_count_bound : AdmissibleCount := by
  intro c₀ c X B h P A hc₀ hc hX hlog hB hBc hh hhc hP hPA
  have hlogpos : 0 < Real.log X := Real.log_pos hX
  have hcpos : 0 < c := lt_of_lt_of_le hlogpos hlog
  have hX0 : 0 < X := by linarith
  have hc0c : (2 : ℝ) ^ 14 ≤ c₀ * c := by
    rw [div_le_iff₀ hc₀] at hc
    linarith
  have hB5 : B ^ 5 ≤ 1024 * c ^ 15 := by
    calc B ^ 5 ≤ (4 * c ^ 3) ^ 5 := pow_le_pow_left₀ hB.le hBc 5
      _ = 1024 * c ^ 15 := by ring
  have hden : h * Real.log X ≤ c ^ 4 := by
    calc h * Real.log X ≤ c ^ 3 * c := mul_le_mul hhc hlog hlogpos.le (pow_pos hcpos 3).le
      _ = c ^ 4 := by ring
  have hB0 : 0 < B ^ 5 := pow_pos hB 5
  have hD0 : 0 < h * Real.log X := mul_pos hh hlogpos
  have hP' : c₀ * X / (1024 * c ^ 19) ≤ P := by
    refine le_trans ?_ hP
    have e : c₀ * B ^ (-5 : ℤ) * X / (h * Real.log X) = c₀ * X / (B ^ 5 * (h * Real.log X)) := by
      rw [zpow_neg, zpow_ofNat]
      field_simp
    rw [e, div_le_div_iff₀ (mul_pos (by norm_num) (pow_pos hcpos 19)) (mul_pos hB0 hD0)]
    have h1 : B ^ 5 * (h * Real.log X) ≤ 1024 * c ^ 19 := by
      calc B ^ 5 * (h * Real.log X) ≤ (1024 * c ^ 15) * c ^ 4 :=
            mul_le_mul hB5 hden hD0.le (mul_pos (by norm_num) (pow_pos hcpos 15)).le
        _ = 1024 * c ^ 19 := by ring
    exact mul_le_mul_of_nonneg_left h1 (mul_pos hc₀ hX0).le
  have hA : 8 * c ^ (-20 : ℤ) * X ≤ c₀ * X / (2048 * c ^ 19) := by
    have e : 8 * c ^ (-20 : ℤ) * X = 8 * X / c ^ 20 := by
      rw [zpow_neg, zpow_ofNat]
      ring
    rw [e, div_le_div_iff₀ (pow_pos hcpos 20) (mul_pos (by norm_num) (pow_pos hcpos 19))]
    nlinarith [mul_nonneg (mul_pos hX0 (pow_pos hcpos 19)).le (sub_nonneg.mpr hc0c)]
  have e2 : c₀ * X / (2048 * c ^ 19) = (c₀ * X / (1024 * c ^ 19)) / 2 := by ring
  calc 8 * c ^ (-20 : ℤ) * X ≤ c₀ * X / (2048 * c ^ 19) := hA
    _ = (c₀ * X / (1024 * c ^ 19)) / 2 := e2
    _ ≤ P / 2 := by linarith
    _ ≤ A := by linarith

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Establish `key : ∀ n : ℕ, ∑ j ∈ Finset.Icc 1 n, (1 / (2 : ℝ) ^ j) = 1 - 1 / 2 ^ n`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[Finset.Icc_eq_empty (by norm_num)]`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega), ih, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`.

Establish `: (0 : ℝ) < 1 / 2 ^ B` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_half_pow_le_one (B : ℕ) : ∑ j ∈ Finset.Icc 1 B, (1 / (2 : ℝ) ^ j) ≤ 1 := by
  have key : ∀ n : ℕ, ∑ j ∈ Finset.Icc 1 n, (1 / (2 : ℝ) ^ j) = 1 - 1 / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      rw [Finset.Icc_eq_empty (by norm_num)]
      simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, pow_succ]
      ring
  rw [key]
  have : (0 : ℝ) < 1 / 2 ^ B := by positivity
  linarith

/- English proof (translation)
Introduce `P X κ hX hκ hP hcard`. Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`. Establish `hκX : 0 < κ * X` using `mul_pos hκ hX`. Take `⟨M, hM⟩` from `exists_pow_lt_of_lt_one (mul_pos (by norm_num : (0 : ℝ) < 2) hκ) (by norm_num : (1 / 2 : ℝ) < 1)`.

Use `set W : ℕ → Finset ℕ := fun j => P.filter (fun p : ℕ => X / 2 ^ j ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * (X / 2 ^ j)) with hW`. Use `set V := (Finset.Icc 1 M).filter (fun j => 2 * κ * X < X / 2 ^ j) with hV`. Establish `hbig : P.filter (fun p : ℕ => 4 * κ * X < p) ⊆ V.biUnion W`. Introduce `p hp`. Rewrite `hp` using `[Finset.mem_filter]`.

Take `⟨hpP, hp4⟩` from `hp`. Establish `h1 : X / 2 ^ M < p`. Establish `e : X / 2 ^ M = X * (1 / 2) ^ M` using `by rw [div_eq_mul_one_div, one_div_pow]`. Rewrite using `[e]`. Establish `: X * (1 / 2) ^ M < X * (2 * κ)` using `mul_lt_mul_of_pos_left hM hX`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hex : ∃ j : ℕ, X / 2 ^ j < p` using `⟨M, h1⟩`. Take `⟨j, hj, hjM, hjmin⟩ : ∃ j : ℕ, X / 2 ^ j < p ∧ j ≤ M ∧ ∀ m < j, ¬ (X / 2 ^ m < p)` from `⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex h1, fun m hm => Nat.find_min hex hm⟩`. Establish `hj1 : 1 ≤ j`. Break down `Nat.eq_zero_or_pos j with h0 | h0` into its components or cases.

Rewrite `hj` using `[h0, pow_zero, div_one]`. Use `(hP p hpP).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h0`. Take `⟨k, hk⟩ : ∃ k, j = k + 1` from `⟨j - 1, by omega⟩`.

Establish `hjprev : (p : ℝ) ≤ 2 * (X / 2 ^ j)`. Establish `h2` using `hjmin k (by omega)`. Use `push_neg at h2`. Establish `e : X / 2 ^ k = 2 * (X / 2 ^ j)`. Rewrite using `[hk, pow_succ]`.

Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion. Use `Finset.mem_biUnion.mpr ⟨j, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hV, Finset.mem_filter, Finset.mem_Icc]`. Use `⟨⟨hj1, hjM⟩, ?_⟩` and prove the remaining obligations.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hW]`. Simplify using `only [Finset.mem_filter]`. Conclude with `⟨hpP, hj.le, hjprev⟩`. Establish `hbigc : ((P.filter (fun p : ℕ => 4 * κ * X < p)).card : ℝ) ≤ κ * X`.

Establish `h1 : (P.filter (fun p : ℕ => 4 * κ * X < p)).card ≤ ∑ j ∈ V, (W j).card` using `(Finset.card_le_card hbig).trans Finset.card_biUnion_le`. Establish `h2 : ∀ j ∈ V, ((W j).card : ℝ) ≤ κ * (X / 2 ^ j)`. Introduce `j hj`. Rewrite `hj` using `[hV, Finset.mem_filter, Finset.mem_Icc]`. Conclude with `(hneg j hj.1.1 hj.2).le`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `h1` after adjusting the coercions. Use `_ ≤ ∑ j ∈ V, κ * (X / 2 ^ j) := Finset.sum_le_sum h2`. Use `_ ≤ ∑ j ∈ Finset.Icc 1 M, κ * (X / 2 ^ j) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => (mul_pos hκ (div_pos hX (by positivity))).le)`. Use `_ = κ * X * ∑ j ∈ Finset.Icc 1 M, (1 / (2 : ℝ) ^ j) := by`.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun j _ => by ring)`. Use `_ ≤ κ * X * 1 := mul_le_mul_of_nonneg_left (sum_half_pow_le_one M) hκX.le`. Use `_ = κ * X := mul_one _`. Establish `hsmall : ((P.filter (fun p : ℕ => ¬ (4 * κ * X < p))).card : ℝ) ≤ 4 * κ * X`.

Establish `hsub : P.filter (fun p : ℕ => ¬ (4 * κ * X < p)) ⊆ Finset.Icc 1 ⌊4 * κ * X⌋₊`. Introduce `p hp`. Rewrite `hp` using `[Finset.mem_filter]`. Rewrite using `[Finset.mem_Icc]`. Use `⟨(hP p hp.1).1, Nat.le_floor ?_⟩` and prove the remaining obligations.

Establish `h` using `hp.2`. Use `push_neg at h`. Conclude with `h`. Combine the equalities or inequalities in the displayed calculation. Establish `htot : ((P.filter (fun p : ℕ => 4 * κ * X < p)).card : ℝ) + ((P.filter (fun p : ℕ => ¬ (4 * κ * X < p))).card : ℝ) = P.card`.

Establish `h` using `Finset.sum_filter_add_sum_filter_not P (fun p : ℕ => 4 * κ * X < p) (fun _ => (1 : ℝ))`. Simplify using `using h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dyadic_window_bound : DyadicWindow := by
  intro P X κ hX hκ hP hcard
  by_contra hneg
  push_neg at hneg
  have hκX : 0 < κ * X := mul_pos hκ hX
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (mul_pos (by norm_num : (0 : ℝ) < 2) hκ)
    (by norm_num : (1 / 2 : ℝ) < 1)
  set W : ℕ → Finset ℕ := fun j =>
    P.filter (fun p : ℕ => X / 2 ^ j ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * (X / 2 ^ j)) with hW
  set V := (Finset.Icc 1 M).filter (fun j => 2 * κ * X < X / 2 ^ j) with hV
  have hbig : P.filter (fun p : ℕ => 4 * κ * X < p) ⊆ V.biUnion W := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpP, hp4⟩ := hp
    have h1 : X / 2 ^ M < p := by
      have e : X / 2 ^ M = X * (1 / 2) ^ M := by rw [div_eq_mul_one_div, one_div_pow]
      rw [e]
      have : X * (1 / 2) ^ M < X * (2 * κ) := mul_lt_mul_of_pos_left hM hX
      linarith
    have hex : ∃ j : ℕ, X / 2 ^ j < p := ⟨M, h1⟩
    classical
    obtain ⟨j, hj, hjM, hjmin⟩ : ∃ j : ℕ, X / 2 ^ j < p ∧ j ≤ M ∧ ∀ m < j, ¬ (X / 2 ^ m < p) :=
      ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex h1, fun m hm => Nat.find_min hex hm⟩
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0, pow_zero, div_one] at hj
        have := (hP p hpP).2
        linarith
      · exact h0
    obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hjprev : (p : ℝ) ≤ 2 * (X / 2 ^ j) := by
      have h2 := hjmin k (by omega)
      push_neg at h2
      have e : X / 2 ^ k = 2 * (X / 2 ^ j) := by
        rw [hk, pow_succ]
        ring
      linarith
    refine Finset.mem_biUnion.mpr ⟨j, ?_, ?_⟩
    · rw [hV, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hj1, hjM⟩, ?_⟩
      linarith
    · rw [hW]
      simp only [Finset.mem_filter]
      exact ⟨hpP, hj.le, hjprev⟩
  have hbigc : ((P.filter (fun p : ℕ => 4 * κ * X < p)).card : ℝ) ≤ κ * X := by
    have h1 : (P.filter (fun p : ℕ => 4 * κ * X < p)).card ≤ ∑ j ∈ V, (W j).card :=
      (Finset.card_le_card hbig).trans Finset.card_biUnion_le
    have h2 : ∀ j ∈ V, ((W j).card : ℝ) ≤ κ * (X / 2 ^ j) := by
      intro j hj
      rw [hV, Finset.mem_filter, Finset.mem_Icc] at hj
      exact (hneg j hj.1.1 hj.2).le
    calc ((P.filter (fun p : ℕ => 4 * κ * X < p)).card : ℝ) ≤ ∑ j ∈ V, ((W j).card : ℝ) := by
          exact_mod_cast h1
      _ ≤ ∑ j ∈ V, κ * (X / 2 ^ j) := Finset.sum_le_sum h2
      _ ≤ ∑ j ∈ Finset.Icc 1 M, κ * (X / 2 ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => (mul_pos hκ (div_pos hX (by positivity))).le)
      _ = κ * X * ∑ j ∈ Finset.Icc 1 M, (1 / (2 : ℝ) ^ j) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ κ * X * 1 := mul_le_mul_of_nonneg_left (sum_half_pow_le_one M) hκX.le
      _ = κ * X := mul_one _
  have hsmall : ((P.filter (fun p : ℕ => ¬ (4 * κ * X < p))).card : ℝ) ≤ 4 * κ * X := by
    have hsub : P.filter (fun p : ℕ => ¬ (4 * κ * X < p)) ⊆ Finset.Icc 1 ⌊4 * κ * X⌋₊ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_Icc]
      refine ⟨(hP p hp.1).1, Nat.le_floor ?_⟩
      have h := hp.2
      push_neg at h
      exact h
    calc ((P.filter (fun p : ℕ => ¬ (4 * κ * X < p))).card : ℝ)
        ≤ ((Finset.Icc 1 ⌊4 * κ * X⌋₊).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = (⌊4 * κ * X⌋₊ : ℝ) := by simp
      _ ≤ 4 * κ * X := Nat.floor_le (by nlinarith)
  have htot : ((P.filter (fun p : ℕ => 4 * κ * X < p)).card : ℝ) +
      ((P.filter (fun p : ℕ => ¬ (4 * κ * X < p))).card : ℝ) = P.card := by
    have h := Finset.sum_filter_add_sum_filter_not P (fun p : ℕ => 4 * κ * X < p) (fun _ => (1 : ℝ))
    simpa using h
  linarith

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `N c X P hN hc hX hmain hP hcard`. Use `set κ := c ^ (-20 : ℤ) with hκdef`. Establish `hc0 : 0 < c` using `by linarith`. Establish `hκ : 0 < κ` using `zpow_pos hc0 _`. Establish `hPX : ∀ p ∈ P, 1 ≤ p ∧ (p : ℝ) ≤ X` using `fun p hp => ⟨(hP p hp).1.one_lt.le, (hP p hp).2⟩`.

Take `⟨j, hj1, hjlt, hjcard⟩` from `hDW P X κ hX hκ hPX hcard`. Use `set Y := X / 2 ^ j with hYdef`. Use `set P' := P.filter (fun p : ℕ => Y ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y) with hP'`. Establish `hκX : 0 < κ * X` using `mul_pos hκ hX`. Establish `hY0 : 0 < Y` using `by linarith`.

Establish `hXY : X * κ ≤ Y` using `by linarith`. Establish `hQ : (N : ℝ) ^ 4 * c ^ 500 ≤ Y ^ ((1 : ℝ) / 4)` using `hmain.trans (Real.rpow_le_rpow (mul_pos hX hκ).le hXY (by norm_num))`. Establish `hN1 : (1 : ℝ) ≤ N` using `by exact_mod_cast (by omega : 1 ≤ N)`. Establish `hN21 : (21 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hc500 : 1 ≤ c ^ 500` using `one_le_pow₀ hc`.

Establish `hN4 : (1 : ℝ) ≤ (N : ℝ) ^ 4` using `one_le_pow₀ hN1`. Establish `hY14 : 1 ≤ Y ^ ((1 : ℝ) / 4)` using `le_trans (one_le_mul_of_one_le_of_one_le hN4 hc500) hQ`. Establish `hY1 : 1 ≤ Y`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Use `Real.rpow_lt_one hY0.le h (by norm_num : (0 : ℝ) < 1 / 4)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsplit : Y = Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4)`. Rewrite using `[← Real.rpow_add hY0]`. Evaluate the numerical expressions.

Establish `hκc : κ * c ^ 500 = c ^ 480`. Rewrite using `[hκdef, zpow_neg, zpow_ofNat, inv_mul_eq_div, div_eq_iff (pow_pos hc0 20).ne']`. Expand and normalize the polynomial expressions, which then agree. Establish `hkey : 20 * (N : ℝ) ^ 3 * Y ^ ((3 : ℝ) / 4) < κ * Y`. Establish `hY34 : 0 < Y ^ ((3 : ℝ) / 4)` using `Real.rpow_pos_of_pos hY0 _`.

Establish `h1 : 20 * (N : ℝ) ^ 3 < κ * Y ^ ((1 : ℝ) / 4)`. Establish `h2 : κ * ((N : ℝ) ^ 4 * c ^ 500) ≤ κ * Y ^ ((1 : ℝ) / 4)` using `mul_le_mul_of_nonneg_left hQ hκ.le`. Establish `h3 : κ * ((N : ℝ) ^ 4 * c ^ 500) = (N : ℝ) ^ 4 * c ^ 480`. Rewrite using `[mul_left_comm, hκc]`. Establish `h4 : (1 : ℝ) ≤ c ^ 480` using `one_le_pow₀ hc`.

Establish `hNpos : (0 : ℝ) < N` using `by linarith`. Establish `h5 : 20 * (N : ℝ) ^ 3 < (N : ℝ) ^ 4`. Use polynomial arithmetic with `[mul_pos (pow_pos hNpos 3) (by linarith : (0 : ℝ) < N - 20)]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h4 (pow_pos hNpos 4).le]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hES'` using `hES N Y (by omega) hY1`. Establish `hmemP' : ∀ g ∈ P', g.Prime ∧ Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y`. Introduce `g hg`. Rewrite `hg` using `[hP', Finset.mem_filter]`. Conclude with `⟨(hP g hg.1).1, hg.2.1, hg.2.2⟩`.

Establish `hcardP' : (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) < P'.card`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨g₁, hg₁, g₂, hg₂, hne, hdisj⟩` from `hP1 N Y P' (by omega) hY1 hmemP' hcardP'`. Establish `hg₁'` using `hmemP' g₁ hg₁`. Establish `hg₂'` using `hmemP' g₂ hg₂`.

Rewrite `hg₁`, `hg₂` using `[hP', Finset.mem_filter]`. Use `⟨Y, hXY, ?_, by linarith, g₁, hg₁.1, g₂, hg₂.1, hne, ⟨hg₁'.2.1, hg₁'.2.2⟩, ⟨hg₂'.2.1, hg₂'.2.2⟩, hdisj⟩` and prove the remaining obligations. Establish `h2j : (2 : ℝ) ≤ 2 ^ j` using `le_self_pow₀ (by norm_num) (by omega)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_le_iff₀ (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem prop1FromCount_of (hDW : DyadicWindow) (hES : ExcludedSimplify) (hP1 : Prop1Core) :
    Prop1FromCount := by
  intro N c X P hN hc hX hmain hP hcard
  set κ := c ^ (-20 : ℤ) with hκdef
  have hc0 : 0 < c := by linarith
  have hκ : 0 < κ := zpow_pos hc0 _
  have hPX : ∀ p ∈ P, 1 ≤ p ∧ (p : ℝ) ≤ X := fun p hp => ⟨(hP p hp).1.one_lt.le, (hP p hp).2⟩
  obtain ⟨j, hj1, hjlt, hjcard⟩ := hDW P X κ hX hκ hPX hcard
  set Y := X / 2 ^ j with hYdef
  set P' := P.filter (fun p : ℕ => Y ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * Y) with hP'
  have hκX : 0 < κ * X := mul_pos hκ hX
  have hY0 : 0 < Y := by linarith
  have hXY : X * κ ≤ Y := by linarith
  have hQ : (N : ℝ) ^ 4 * c ^ 500 ≤ Y ^ ((1 : ℝ) / 4) :=
    hmain.trans (Real.rpow_le_rpow (mul_pos hX hκ).le hXY (by norm_num))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN21 : (21 : ℝ) ≤ N := by exact_mod_cast hN
  have hc500 : 1 ≤ c ^ 500 := one_le_pow₀ hc
  have hN4 : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ hN1
  have hY14 : 1 ≤ Y ^ ((1 : ℝ) / 4) := le_trans (one_le_mul_of_one_le_of_one_le hN4 hc500) hQ
  have hY1 : 1 ≤ Y := by
    by_contra h
    push_neg at h
    have := Real.rpow_lt_one hY0.le h (by norm_num : (0 : ℝ) < 1 / 4)
    linarith
  have hsplit : Y = Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hY0]
    norm_num
  have hκc : κ * c ^ 500 = c ^ 480 := by
    rw [hκdef, zpow_neg, zpow_ofNat, inv_mul_eq_div, div_eq_iff (pow_pos hc0 20).ne']
    ring
  have hkey : 20 * (N : ℝ) ^ 3 * Y ^ ((3 : ℝ) / 4) < κ * Y := by
    have hY34 : 0 < Y ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hY0 _
    have h1 : 20 * (N : ℝ) ^ 3 < κ * Y ^ ((1 : ℝ) / 4) := by
      have h2 : κ * ((N : ℝ) ^ 4 * c ^ 500) ≤ κ * Y ^ ((1 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left hQ hκ.le
      have h3 : κ * ((N : ℝ) ^ 4 * c ^ 500) = (N : ℝ) ^ 4 * c ^ 480 := by
        rw [mul_left_comm, hκc]
      have h4 : (1 : ℝ) ≤ c ^ 480 := one_le_pow₀ hc
      have hNpos : (0 : ℝ) < N := by linarith
      have h5 : 20 * (N : ℝ) ^ 3 < (N : ℝ) ^ 4 := by
        nlinarith [mul_pos (pow_pos hNpos 3) (by linarith : (0 : ℝ) < N - 20)]
      nlinarith [mul_le_mul_of_nonneg_left h4 (pow_pos hNpos 4).le]
    calc 20 * (N : ℝ) ^ 3 * Y ^ ((3 : ℝ) / 4) < κ * Y ^ ((1 : ℝ) / 4) * Y ^ ((3 : ℝ) / 4) :=
          mul_lt_mul_of_pos_right h1 hY34
      _ = κ * (Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4)) := by ring
      _ = κ * Y := by rw [← hsplit]
  have hES' := hES N Y (by omega) hY1
  have hmemP' : ∀ g ∈ P', g.Prime ∧ Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y := by
    intro g hg
    rw [hP', Finset.mem_filter] at hg
    exact ⟨(hP g hg.1).1, hg.2.1, hg.2.2⟩
  have hcardP' : (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) < P'.card := by
    linarith
  obtain ⟨g₁, hg₁, g₂, hg₂, hne, hdisj⟩ := hP1 N Y P' (by omega) hY1 hmemP' hcardP'
  have hg₁' := hmemP' g₁ hg₁
  have hg₂' := hmemP' g₂ hg₂
  rw [hP', Finset.mem_filter] at hg₁ hg₂
  refine ⟨Y, hXY, ?_, by linarith, g₁, hg₁.1, g₂, hg₂.1, hne, ⟨hg₁'.2.1, hg₁'.2.2⟩,
    ⟨hg₂'.2.1, hg₂'.2.2⟩, hdisj⟩
  have h2j : (2 : ℝ) ≤ 2 ^ j := le_self_pow₀ (by norm_num) (by omega)
  calc 2 * Y = 2 * X / 2 ^ j := by rw [hYdef]; ring
    _ ≤ X := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Proceed by induction on `d using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Establish `ha : 1 ≤ a` using `hd a (Multiset.mem_cons_self a s)`. Establish `hs : ∀ x ∈ s, 1 ≤ x` using `fun x hx => hd x (Multiset.mem_cons_of_mem hx)`.

Simplify using `only [Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons, Nat.cast_add] at h2 ⊢`. Establish `ha' : (1 : ℝ) ≤ a` using `by exact_mod_cast ha`. Establish `hs0 : (0 : ℝ) ≤ s.sum` using `Nat.cast_nonneg _`. Establish `ih'` using `ih hs (by linarith)`. Establish `hG0 : 0 < G` using `by linarith`.

Establish `hGa : G ≤ G ^ a` using `le_self_pow₀ (by linarith) (by omega)`. Establish `hGa0 : 0 ≤ G ^ a` using `(pow_pos hG0 a).le`. Establish `hP0 : 0 ≤ (s.map (fun x => G ^ x - 1)).prod`. Apply `Multiset.prod_nonneg` to reduce the goal to its premises. Introduce `y hy`.

Take `⟨x, hx, rfl⟩` from `Multiset.mem_map.mp hy`. Establish `: 1 ≤ G ^ x` using `one_le_pow₀ (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : G ^ a * (1 + 2 * (s.sum : ℝ) / G) ≤ (1 + 2 * ((a : ℝ) + s.sum) / G) * (G ^ a - 1)`. Rewrite using `[← sub_nonneg]`.

Establish `e : (1 + 2 * ((a : ℝ) + s.sum) / G) * (G ^ a - 1) - G ^ a * (1 + 2 * (s.sum : ℝ) / G) = (2 * a * G ^ a - G - 2 * (a + s.sum)) / G`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Apply `div_nonneg _ hG0.le` to reduce the goal to its premises.

Use polynomial arithmetic with `[mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1) hGa0]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem lw_lemma (G : ℝ) (hG : 2 ≤ G) (d : Multiset ℕ) (hd : ∀ x ∈ d, 1 ≤ x)
    (h2 : 2 * (d.sum : ℝ) ≤ G) :
    G ^ d.sum ≤ (1 + 2 * (d.sum : ℝ) / G) * (d.map (fun x => G ^ x - 1)).prod := by
  induction d using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : 1 ≤ a := hd a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, 1 ≤ x := fun x hx => hd x (Multiset.mem_cons_of_mem hx)
    simp only [Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons, Nat.cast_add] at h2 ⊢
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hs0 : (0 : ℝ) ≤ s.sum := Nat.cast_nonneg _
    have ih' := ih hs (by linarith)
    have hG0 : 0 < G := by linarith
    have hGa : G ≤ G ^ a := le_self_pow₀ (by linarith) (by omega)
    have hGa0 : 0 ≤ G ^ a := (pow_pos hG0 a).le
    have hP0 : 0 ≤ (s.map (fun x => G ^ x - 1)).prod := by
      apply Multiset.prod_nonneg
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      have : 1 ≤ G ^ x := one_le_pow₀ (by linarith)
      linarith
    have key : G ^ a * (1 + 2 * (s.sum : ℝ) / G) ≤
        (1 + 2 * ((a : ℝ) + s.sum) / G) * (G ^ a - 1) := by
      rw [← sub_nonneg]
      have e : (1 + 2 * ((a : ℝ) + s.sum) / G) * (G ^ a - 1) - G ^ a * (1 + 2 * (s.sum : ℝ) / G)
          = (2 * a * G ^ a - G - 2 * (a + s.sum)) / G := by
        field_simp
        ring
      rw [e]
      apply div_nonneg _ hG0.le
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1) hGa0]
    calc G ^ (a + s.sum) = G ^ a * G ^ s.sum := pow_add _ _ _
      _ ≤ G ^ a * ((1 + 2 * (s.sum : ℝ) / G) * (s.map (fun x => G ^ x - 1)).prod) :=
          mul_le_mul_of_nonneg_left ih' hGa0
      _ = (G ^ a * (1 + 2 * (s.sum : ℝ) / G)) * (s.map (fun x => G ^ x - 1)).prod := by ring
      _ ≤ ((1 + 2 * ((a : ℝ) + s.sum) / G) * (G ^ a - 1)) * (s.map (fun x => G ^ x - 1)).prod :=
          mul_le_mul_of_nonneg_right key hP0
      _ = _ := by ring

/- English proof (translation)
Proceed by induction on `d using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Establish `ha : 1 ≤ a` using `hd a (Multiset.mem_cons_self a s)`. Take `⟨ih1, ih2⟩` from `ih (fun x hx => hd x (Multiset.mem_cons_of_mem hx))`.

Simplify using `only [Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons]`. Establish `hGa : G ≤ G ^ a` using `le_self_pow₀ (by linarith) (by omega)`. Use `⟨mul_pos (by linarith) ih1, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add]`. Conclude with `mul_le_mul (by linarith) ih2 ih1.le (pow_pos (by linarith) a).le`.
-/
private theorem lw_lemma_2 (G : ℝ) (hG : 2 ≤ G) (d : Multiset ℕ) (hd : ∀ x ∈ d, 1 ≤ x) :
    0 < (d.map (fun x => G ^ x - 1)).prod ∧ (d.map (fun x => G ^ x - 1)).prod ≤ G ^ d.sum := by
  induction d using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : 1 ≤ a := hd a (Multiset.mem_cons_self a s)
    obtain ⟨ih1, ih2⟩ := ih (fun x hx => hd x (Multiset.mem_cons_of_mem hx))
    simp only [Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons]
    have hGa : G ≤ G ^ a := le_self_pow₀ (by linarith) (by omega)
    refine ⟨mul_pos (by linarith) ih1, ?_⟩
    rw [pow_add]
    exact mul_le_mul (by linarith) ih2 ih1.le (pow_pos (by linarith) a).le

/- English proof (translation)
Introduce `d g hd hg`. Establish `hG : (2 : ℝ) ≤ g` using `by exact_mod_cast hg`. Take `⟨hP, hle⟩` from `lw_lemma_2 (g : ℝ) hG d hd`. Establish `hpow : (0 : ℝ) < (g : ℝ) ^ d.sum` using `pow_pos (by linarith) _`. Use `⟨one_div_le_one_div_of_le hP hle, fun h2 => ?_⟩` and prove the remaining obligations.

Establish `h2' : 2 * (d.sum : ℝ) ≤ g` using `by exact_mod_cast h2`. Establish `key` using `lw_lemma (g : ℝ) hG d hd h2'`. Rewrite using `[div_le_div_iff₀ hP hpow, one_mul]`. Conclude with `key`.
-/
theorem lemma_L_weight_upper_unit : LemmaLWeightU := by
  intro d g hd hg
  have hG : (2 : ℝ) ≤ g := by exact_mod_cast hg
  obtain ⟨hP, hle⟩ := lw_lemma_2 (g : ℝ) hG d hd
  have hpow : (0 : ℝ) < (g : ℝ) ^ d.sum := pow_pos (by linarith) _
  refine ⟨one_div_le_one_div_of_le hP hle, fun h2 => ?_⟩
  have h2' : 2 * (d.sum : ℝ) ≤ g := by exact_mod_cast h2
  have key := lw_lemma (g : ℝ) hG d hd h2'
  rw [div_le_div_iff₀ hP hpow, one_mul]
  exact key

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `g D Nd n hg hD hN`. Rewrite using `[one_div, ← Finset.prod_inv_distrib]`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `d hd`. Establish `hgd : (1 : ℝ) ≤ (g : ℝ) ^ d` using `one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ g))`.

Conclude with `div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)`. Introduce `d hd`. Establish `hd1` using `hD d hd`. Establish `hgd : (1 : ℝ) < (g : ℝ) ^ d` using `one_lt_pow₀ (by exact_mod_cast (by omega : 1 < g)) (by omega)`. Establish `hNd : (d : ℝ) * (Nd d : ℝ) ≤ (g : ℝ) ^ d - 1`.

Establish `h` using `hN d hd`. Establish `h1 : 1 ≤ g ^ d` using `Nat.one_le_pow _ _ (by omega)`. Establish `h2 : ((d * Nd d : ℕ) : ℝ) ≤ ((g ^ d - 1 : ℕ) : ℝ)` using `by exact_mod_cast h`. Rewrite `h2` using `[Nat.cast_sub h1]`. Move the coercions through the operations in `at h2`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpos : (0 : ℝ) < (g : ℝ) ^ d - 1` using `by linarith`. Establish `hdpos : (0 : ℝ) < d` using `by exact_mod_cast (by omega : 0 < d)`. Establish `hfact : (0 : ℝ) < ((n d).factorial : ℝ)` using `by exact_mod_cast Nat.factorial_pos _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[div_div, inv_eq_one_div, div_le_div_iff₀ (mul_pos hfact (pow_pos hpos _)) (mul_pos (pow_pos hdpos _) hfact), one_mul]`. Establish `hp : ((d : ℝ) * Nd d) ^ (n d) ≤ ((g : ℝ) ^ d - 1) ^ (n d)` using `pow_le_pow_left₀ (by positivity) hNd _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem type_weight_upper_unit : TypeWeightU := by
  intro g D Nd n hg hD hN
  rw [one_div, ← Finset.prod_inv_distrib]
  apply Finset.prod_le_prod
  · intro d hd
    have hgd : (1 : ℝ) ≤ (g : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ g))
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)
  · intro d hd
    have hd1 := hD d hd
    have hgd : (1 : ℝ) < (g : ℝ) ^ d := one_lt_pow₀ (by exact_mod_cast (by omega : 1 < g)) (by omega)
    have hNd : (d : ℝ) * (Nd d : ℝ) ≤ (g : ℝ) ^ d - 1 := by
      have h := hN d hd
      have h1 : 1 ≤ g ^ d := Nat.one_le_pow _ _ (by omega)
      have h2 : ((d * Nd d : ℕ) : ℝ) ≤ ((g ^ d - 1 : ℕ) : ℝ) := by exact_mod_cast h
      rw [Nat.cast_sub h1] at h2
      push_cast at h2
      linarith
    have hpos : (0 : ℝ) < (g : ℝ) ^ d - 1 := by linarith
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hfact : (0 : ℝ) < ((n d).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    calc ((Nd d).choose (n d) : ℝ) / ((g : ℝ) ^ d - 1) ^ (n d)
        ≤ ((Nd d : ℝ) ^ (n d) / ((n d).factorial : ℝ)) / ((g : ℝ) ^ d - 1) ^ (n d) :=
          div_le_div_of_nonneg_right (Nat.choose_le_pow_div _ _) (pow_nonneg hpos.le _)
      _ ≤ ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ))⁻¹ := by
          rw [div_div, inv_eq_one_div, div_le_div_iff₀ (mul_pos hfact (pow_pos hpos _))
            (mul_pos (pow_pos hdpos _) hfact), one_mul]
          have hp : ((d : ℝ) * Nd d) ^ (n d) ≤ ((g : ℝ) ^ d - 1) ^ (n d) :=
            pow_le_pow_left₀ (by positivity) hNd _
          calc (Nd d : ℝ) ^ (n d) * ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ))
              = ((d : ℝ) * Nd d) ^ (n d) * ((n d).factorial : ℝ) := by ring
            _ ≤ ((g : ℝ) ^ d - 1) ^ (n d) * ((n d).factorial : ℝ) :=
                mul_le_mul_of_nonneg_right hp hfact.le
            _ = ((n d).factorial : ℝ) * ((g : ℝ) ^ d - 1) ^ (n d) := by ring

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `ι _ _ T _ wU wJ g A hg hU0 hU1 hJ1 hJU`. Establish `hg0 : 0 < g` using `by linarith`. Establish `hgi : 1 / g ≤ 1` using `(div_le_one hg0).2 hg`. Establish `hgi0 : 0 ≤ 1 / g` using `by positivity`. Use `set a : ℝ := 1 - 1 / g with ha`.

Establish `ha0 : 0 ≤ a` using `by rw [ha]; linarith`. Establish `ha1 : a ≤ 1` using `by rw [ha]; linarith`. Establish `htot : ∀ w : ∀ v, T v → ℝ, (∀ v, ∑ t, w v t = 1) → ∑ x : (∀ v, T v), ∏ v, w v (x v) = 1`. Introduce `w hw`. Rewrite using `[← Fintype.piFinset_univ, ← Finset.prod_univ_sum]`.

Simplify using `[hw]`. Establish `hprod : ∀ x : (∀ v, T v), a ^ Fintype.card ι * ∏ v, wU v (x v) ≤ ∏ v, wJ v (x v)`. Introduce `x`. Rewrite using `[← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_le_prod (fun v _ => mul_nonneg ha0 (hU0 v _)) (fun v _ => hJU v _)`.

Establish `hsJ` using `Finset.sum_sdiff (f := fun x => ∏ v, wJ v (x v)) (Finset.subset_univ A)`. Establish `hsU` using `Finset.sum_sdiff (f := fun x => ∏ v, wU v (x v)) (Finset.subset_univ A)`. Rewrite `hsJ` using `[htot wJ hJ1]`. Rewrite `hsU` using `[htot wU hU1]`. Establish `hcomp : a ^ Fintype.card ι * ∑ x ∈ Finset.univ \ A, ∏ v, wU v (x v) ≤ ∑ x ∈ Finset.univ \ A, ∏ v, wJ v (x v)`.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_le_sum (fun x _ => hprod x)`. Establish `hA0 : 0 ≤ ∑ x ∈ A, ∏ v, wU v (x v)` using `Finset.sum_nonneg (fun x _ => Finset.prod_nonneg (fun v _ => hU0 v _))`. Establish `hbern : 1 - (Fintype.card ι : ℝ) / g ≤ a ^ Fintype.card ι`. Establish `h` using `one_add_mul_le_pow (a := -(1 / g)) (by linarith) (Fintype.card ι)`.

Establish `e1 : 1 + (Fintype.card ι : ℝ) * -(1 / g) = 1 - (Fintype.card ι : ℝ) / g` using `by ring`. Establish `e2 : 1 + -(1 / g) = a` using `by rw [ha]; ring`. Rewrite `h` using `[e1, e2]`. Conclude with `h`. Establish `hpow1 : a ^ Fintype.card ι ≤ 1` using `pow_le_one₀ ha0 ha1`.

Establish `hc : ∑ x ∈ Finset.univ \ A, ∏ v, wU v (x v) = 1 - ∑ x ∈ A, ∏ v, wU v (x v)` using `by linarith`. Rewrite `hcomp` using `[hc]`. Establish `hm` using `mul_le_mul_of_nonneg_right hpow1 hA0`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem comparison_transfer_holds : ComparisonTransfer := by
  intro ι _ _ T _ wU wJ g A hg hU0 hU1 hJ1 hJU
  classical
  have hg0 : 0 < g := by linarith
  have hgi : 1 / g ≤ 1 := (div_le_one hg0).2 hg
  have hgi0 : 0 ≤ 1 / g := by positivity
  set a : ℝ := 1 - 1 / g with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have ha1 : a ≤ 1 := by rw [ha]; linarith
  have htot : ∀ w : ∀ v, T v → ℝ, (∀ v, ∑ t, w v t = 1) →
      ∑ x : (∀ v, T v), ∏ v, w v (x v) = 1 := by
    intro w hw
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
    simp [hw]
  have hprod : ∀ x : (∀ v, T v), a ^ Fintype.card ι * ∏ v, wU v (x v) ≤ ∏ v, wJ v (x v) := by
    intro x
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun v _ => mul_nonneg ha0 (hU0 v _)) (fun v _ => hJU v _)
  have hsJ := Finset.sum_sdiff (f := fun x => ∏ v, wJ v (x v)) (Finset.subset_univ A)
  have hsU := Finset.sum_sdiff (f := fun x => ∏ v, wU v (x v)) (Finset.subset_univ A)
  rw [htot wJ hJ1] at hsJ
  rw [htot wU hU1] at hsU
  have hcomp : a ^ Fintype.card ι * ∑ x ∈ Finset.univ \ A, ∏ v, wU v (x v) ≤
      ∑ x ∈ Finset.univ \ A, ∏ v, wJ v (x v) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun x _ => hprod x)
  have hA0 : 0 ≤ ∑ x ∈ A, ∏ v, wU v (x v) :=
    Finset.sum_nonneg (fun x _ => Finset.prod_nonneg (fun v _ => hU0 v _))
  have hbern : 1 - (Fintype.card ι : ℝ) / g ≤ a ^ Fintype.card ι := by
    have h := one_add_mul_le_pow (a := -(1 / g)) (by linarith) (Fintype.card ι)
    have e1 : 1 + (Fintype.card ι : ℝ) * -(1 / g) = 1 - (Fintype.card ι : ℝ) / g := by ring
    have e2 : 1 + -(1 / g) = a := by rw [ha]; ring
    rw [e1, e2] at h
    exact h
  have hpow1 : a ^ Fintype.card ι ≤ 1 := pow_le_one₀ ha0 ha1
  have hc : ∑ x ∈ Finset.univ \ A, ∏ v, wU v (x v) = 1 - ∑ x ∈ A, ∏ v, wU v (x v) := by linarith
  rw [hc] at hcomp
  have hm := mul_le_mul_of_nonneg_right hpow1 hA0
  nlinarith

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `g δ hg hδ`. Establish `hgδ : 2 ≤ g ^ δ` using `le_trans hg (Nat.le_self_pow (by omega) g)`. Establish `h1 : 2 ^ (g ^ δ - 1).primeFactors.card ≤ g ^ δ - 1`. Combine the equalities or inequalities in the displayed calculation. Establish `key : (2 : ℝ) ^ (g ^ δ - 1).primeFactors.card ≤ (g : ℝ) ^ δ`.

Establish `h2 : 2 ^ (g ^ δ - 1).primeFactors.card ≤ g ^ δ` using `by omega`. Conclude with `h2` after adjusting the coercions. Establish `hg0 : (0 : ℝ) < g` using `by exact_mod_cast (by omega : 0 < g)`. Rewrite using `[← Real.logb_pow, Real.le_logb_iff_rpow_le (by norm_num) (pow_pos hg0 _), Real.rpow_natCast]`. Conclude with `key`.
-/
theorem prime_factors_log_two_bound : PrimeFactorsLogTwo := by
  intro g δ hg hδ
  have hgδ : 2 ≤ g ^ δ := le_trans hg (Nat.le_self_pow (by omega) g)
  have h1 : 2 ^ (g ^ δ - 1).primeFactors.card ≤ g ^ δ - 1 := by
    calc 2 ^ (g ^ δ - 1).primeFactors.card ≤ ∏ p ∈ (g ^ δ - 1).primeFactors, p :=
          Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ g ^ δ - 1 := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd _)
  have key : (2 : ℝ) ^ (g ^ δ - 1).primeFactors.card ≤ (g : ℝ) ^ δ := by
    have h2 : 2 ^ (g ^ δ - 1).primeFactors.card ≤ g ^ δ := by omega
    exact_mod_cast h2
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  rw [← Real.logb_pow, Real.le_logb_iff_rpow_le (by norm_num) (pow_pos hg0 _), Real.rpow_natCast]
  exact key

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `u N hu0 hu8`. Prove the components needed by the constructor for the conclusion. Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Simplify using `only [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 2), Finset.sum_empty]`. Check the signs of the components of the expression.

Establish `key : ∀ n, 1 ≤ n → ∑ δ ∈ Finset.Icc (2 : ℕ) n, ((δ : ℕ) : ℝ) * u ^ δ + u ^ (n + 1) * (8 / 7 * (n : ℝ) + 64 / 49) ≤ 6 * u ^ 2`. Introduce `n hn`. Proceed by induction on `n, hn using Nat.le_induction with`. Consider the case `base`. Simplify using `only [Finset.Icc_eq_empty_of_lt (by norm_num : (1 : ℕ) < 2), Finset.sum_empty]`.

Evaluate the numerical expressions. Use polynomial arithmetic with `[sq_nonneg u]`. Consider the case `succ n hn ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega)]`. Move the coercions through the operations in `at ih ⊢`.

Establish `hun : 0 ≤ u ^ (n + 1)` using `pow_nonneg hu0 _`. Establish `hp : 0 ≤ 8 / 7 * ((n : ℝ) + 1) + 64 / 49` using `by positivity`. Establish `hw : u ^ (n + 1 + 1) = u ^ (n + 1) * u` using `pow_succ _ _`. Rewrite using `[hw]`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg hun hp) (sub_nonneg.2 hu8)]`.

Establish `h1` using `key N hN`. Establish `h2 : 0 ≤ u ^ (N + 1) * (8 / 7 * (N : ℝ) + 64 / 49)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : ∀ n, ∑ δ ∈ Finset.Icc (1 : ℕ) n, ((δ : ℕ) : ℝ) ^ 2 * u ^ δ + u ^ (n + 1) * (8 / 7 * (n : ℝ) ^ 2 + 128 / 49 * n + 576 / 343) ≤ 17 / 10 * u`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Simplify using `only [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.sum_empty]`. Evaluate the numerical expressions. Use the polynomial consequences of the given equalities and inequalities.

Consider the case `succ n ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega)]`. Move the coercions through the operations in `at ih ⊢`. Establish `hun : 0 ≤ u ^ (n + 1)` using `pow_nonneg hu0 _`. Establish `hp : 0 ≤ 8 / 7 * ((n : ℝ) + 1) ^ 2 + 128 / 49 * ((n : ℝ) + 1) + 576 / 343`.

Check the signs of the components of the expression. Establish `hw : u ^ (n + 1 + 1) = u ^ (n + 1) * u` using `pow_succ _ _`. Rewrite using `[hw]`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg hun hp) (sub_nonneg.2 hu8)]`. Establish `h1` using `key N`.

Establish `h2 : 0 ≤ u ^ (N + 1) * (8 / 7 * (N : ℝ) ^ 2 + 128 / 49 * N + 576 / 343)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem series_bounds_hold : SeriesBounds := by
  intro u N hu0 hu8
  constructor
  · rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 2), Finset.sum_empty]
      positivity
    · have key : ∀ n, 1 ≤ n → ∑ δ ∈ Finset.Icc (2 : ℕ) n, ((δ : ℕ) : ℝ) * u ^ δ +
          u ^ (n + 1) * (8 / 7 * (n : ℝ) + 64 / 49) ≤ 6 * u ^ 2 := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base =>
          simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (1 : ℕ) < 2), Finset.sum_empty]
          norm_num
          nlinarith [sq_nonneg u]
        | succ n hn ih =>
          rw [Finset.sum_Icc_succ_top (by omega)]
          push_cast at ih ⊢
          have hun : 0 ≤ u ^ (n + 1) := pow_nonneg hu0 _
          have hp : 0 ≤ 8 / 7 * ((n : ℝ) + 1) + 64 / 49 := by positivity
          have hw : u ^ (n + 1 + 1) = u ^ (n + 1) * u := pow_succ _ _
          rw [hw]
          nlinarith [mul_nonneg (mul_nonneg hun hp) (sub_nonneg.2 hu8)]
      have h1 := key N hN
      have h2 : 0 ≤ u ^ (N + 1) * (8 / 7 * (N : ℝ) + 64 / 49) := by positivity
      linarith
  · have key : ∀ n, ∑ δ ∈ Finset.Icc (1 : ℕ) n, ((δ : ℕ) : ℝ) ^ 2 * u ^ δ +
        u ^ (n + 1) * (8 / 7 * (n : ℝ) ^ 2 + 128 / 49 * n + 576 / 343) ≤ 17 / 10 * u := by
      intro n
      induction n with
      | zero =>
        simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), Finset.sum_empty]
        norm_num
        nlinarith
      | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        push_cast at ih ⊢
        have hun : 0 ≤ u ^ (n + 1) := pow_nonneg hu0 _
        have hp : 0 ≤ 8 / 7 * ((n : ℝ) + 1) ^ 2 + 128 / 49 * ((n : ℝ) + 1) + 576 / 343 := by
          positivity
        have hw : u ^ (n + 1 + 1) = u ^ (n + 1) * u := pow_succ _ _
        rw [hw]
        nlinarith [mul_nonneg (mul_nonneg hun hp) (sub_nonneg.2 hu8)]
    have h1 := key N
    have h2 : 0 ≤ u ^ (N + 1) * (8 / 7 * (N : ℝ) ^ 2 + 128 / 49 * N + 576 / 343) := by positivity
    linarith

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `ε W₁ W₂ PP₁ PP₂ D₁ D₂ Dall Dstar bad hε0 hε1 hD hP1 hPW1 hP2 hPW2 hall h1 h2 hbad`. Establish `hall' : (1 - ε) * Dstar ≤ Dall`. Use `(abs_le.mp hall).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1e : 0 < 1 - ε` using `by linarith`.

Establish `hDall : 0 < Dall` using `lt_of_lt_of_le (mul_pos h1e hD) hall'`. Establish `hd1 : D₁ ≤ (1 + ε) * W₁ * Dstar`. Use `(abs_le.mp h1).2` as an intermediate fact. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) hD.le) (sub_nonneg.mpr hPW1)]`. Establish `hd2 : D₂ ≤ (1 + ε) * W₂ * Dstar`.

Use `(abs_le.mp h2).2` as an intermediate fact. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) hD.le) (sub_nonneg.mpr hPW2)]`. Establish `hW : 0 ≤ W₁ + W₂` using `by linarith`. Establish `hne : 1 - ε ≠ 0` using `h1e.ne'`. Establish `hc : 0 ≤ (1 + ε) / (1 - ε) * (W₁ + W₂)` using `mul_nonneg (div_nonneg (by linarith) h1e.le) hW`.

Rewrite using `[div_le_iff₀ hDall]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show (1 + ε) / (1 - ε) * (W₁ + W₂) * ((1 - ε) * Dstar) = (1 + ε) * (W₁ + W₂) * Dstar * ((1 - ε) / (1 - ε)) by ring, div_self hne, mul_one]`. Use `_ ≤ (1 + ε) / (1 - ε) * (W₁ + W₂) * Dall := mul_le_mul_of_nonneg_left hall' hc`.
-/
theorem share_from_count : ShareFromCount := by
  intro ε W₁ W₂ PP₁ PP₂ D₁ D₂ Dall Dstar bad hε0 hε1 hD hP1 hPW1 hP2 hPW2 hall h1 h2 hbad
  have hall' : (1 - ε) * Dstar ≤ Dall := by
    have := (abs_le.mp hall).1
    linarith
  have h1e : 0 < 1 - ε := by linarith
  have hDall : 0 < Dall := lt_of_lt_of_le (mul_pos h1e hD) hall'
  have hd1 : D₁ ≤ (1 + ε) * W₁ * Dstar := by
    have := (abs_le.mp h1).2
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) hD.le) (sub_nonneg.mpr hPW1)]
  have hd2 : D₂ ≤ (1 + ε) * W₂ * Dstar := by
    have := (abs_le.mp h2).2
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) hD.le) (sub_nonneg.mpr hPW2)]
  have hW : 0 ≤ W₁ + W₂ := by linarith
  have hne : 1 - ε ≠ 0 := h1e.ne'
  have hc : 0 ≤ (1 + ε) / (1 - ε) * (W₁ + W₂) :=
    mul_nonneg (div_nonneg (by linarith) h1e.le) hW
  rw [div_le_iff₀ hDall]
  calc bad ≤ (1 + ε) * (W₁ + W₂) * Dstar := by linarith
    _ = (1 + ε) / (1 - ε) * (W₁ + W₂) * ((1 - ε) * Dstar) := by
        rw [show (1 + ε) / (1 - ε) * (W₁ + W₂) * ((1 - ε) * Dstar)
            = (1 + ε) * (W₁ + W₂) * Dstar * ((1 - ε) / (1 - ε)) by ring, div_self hne, mul_one]
    _ ≤ (1 + ε) / (1 - ε) * (W₁ + W₂) * Dall := mul_le_mul_of_nonneg_left hall' hc

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Filter Topology in
/- English proof (translation)
Introduce `C ε hε`. Establish `hε0 : ε ≠ 0` using `hε.ne'`. Establish `ha : 0 < ε / 6` using `by positivity`. Establish `hab : 0 < ε / 6 - ε / 7` using `by linarith`. Establish `hA : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x ^ (ε / 6 - ε / 7)` using `(tendsto_rpow_atTop hab).eventually_ge_atTop 2`.

Establish `hB : ∀ᶠ x : ℝ in Filter.atTop, (x ^ (ε / 6)) ^ (C / (ε / 6)) * Real.exp (-(1 / 2) * x ^ (ε / 6)) < 1 / 8`. Establish `h` using `(tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (C / (ε / 6)) (1 / 2) (by norm_num)).comp (tendsto_rpow_atTop ha)`. Conclude with `h.eventually (gt_mem_nhds (by norm_num))`. Use `filter_upwards [hA, hB, Filter.eventually_gt_atTop 0] with x hxA hxB hx0`. Establish `hxa : x ^ (ε / 6) = x ^ (ε / 6 - ε / 7) * x ^ (ε / 7)`.

Rewrite using `[← Real.rpow_add hx0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hpow : (x ^ (ε / 6)) ^ (C / (ε / 6)) = x ^ C`. Rewrite using `[← Real.rpow_mul hx0.le]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hxb0 : 0 < x ^ (ε / 7)` using `Real.rpow_pos_of_pos hx0 _`. Establish `hle : x ^ (ε / 7) ≤ x ^ (ε / 6) / 2`. Rewrite using `[hxa]`.

Use the polynomial consequences of the given equalities and inequalities. Rewrite `hxB` using `[hpow]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, ← Real.exp_add]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ 1 / 8 * Real.exp (-(1 / 2) * x ^ (ε / 6)) := mul_le_mul_of_nonneg_right hxB.le (Real.exp_pos _).le`. Use `_ ≤ 1 / 8 * Real.exp (-x ^ (ε / 7)) := by`. Apply `mul_le_mul_of_nonneg_left _ (by norm_num)` to reduce the goal to its premises. Conclude with `Real.exp_le_exp.mpr (by linarith)`.
-/
theorem dominant_numbers_bound : NumbersDominant := by
  intro C ε hε
  have hε0 : ε ≠ 0 := hε.ne'
  have ha : 0 < ε / 6 := by positivity
  have hab : 0 < ε / 6 - ε / 7 := by linarith
  have hA : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x ^ (ε / 6 - ε / 7) :=
    (tendsto_rpow_atTop hab).eventually_ge_atTop 2
  have hB : ∀ᶠ x : ℝ in Filter.atTop,
      (x ^ (ε / 6)) ^ (C / (ε / 6)) * Real.exp (-(1 / 2) * x ^ (ε / 6)) < 1 / 8 := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (C / (ε / 6)) (1 / 2)
      (by norm_num)).comp (tendsto_rpow_atTop ha)
    exact h.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hA, hB, Filter.eventually_gt_atTop 0] with x hxA hxB hx0
  have hxa : x ^ (ε / 6) = x ^ (ε / 6 - ε / 7) * x ^ (ε / 7) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hpow : (x ^ (ε / 6)) ^ (C / (ε / 6)) = x ^ C := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  have hxb0 : 0 < x ^ (ε / 7) := Real.rpow_pos_of_pos hx0 _
  have hle : x ^ (ε / 7) ≤ x ^ (ε / 6) / 2 := by
    rw [hxa]
    nlinarith
  rw [hpow] at hxB
  calc x ^ C * Real.exp (-x ^ (ε / 6))
      = x ^ C * Real.exp (-(1 / 2) * x ^ (ε / 6)) * Real.exp (-(1 / 2) * x ^ (ε / 6)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
    _ ≤ 1 / 8 * Real.exp (-(1 / 2) * x ^ (ε / 6)) :=
        mul_le_mul_of_nonneg_right hxB.le (Real.exp_pos _).le
    _ ≤ 1 / 8 * Real.exp (-x ^ (ε / 7)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.exp_le_exp.mpr (by linarith)

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

attribute [-instance] AddCommGroup.toIntModule in
/- English proof (translation)
Use `set b := Module.Free.chooseBasis ℤ S`. Rewrite using `[Algebra.norm_eq_matrix_det b, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, RingHom.map_det, map_one, sub_eq_zero]`. Establish `hc : (Ideal.Quotient.mk (Ideal.span {c})) c = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c)`. Establish `h0 : (Ideal.Quotient.mk (Ideal.span {c})).mapMatrix (algebraMap ℤ (Matrix (Module.Free.ChooseBasisIndex ℤ S) (Module.Free.ChooseBasisIndex ℤ S) ℤ) c) = 0`. Use extensionality with `i j`.

Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]`. Apply the tactic sequence `split_ifs <;> simp [hc]`. Rewrite using `[map_add, map_one, map_mul, AlgHom.commutes, map_add, map_one, map_mul, h0, zero_mul, add_zero, Matrix.det_one]`.
-/
theorem norm_one_add_mul (S : Type) [CommRing S] [Algebra ℤ S] [Module.Free ℤ S]
    [Module.Finite ℤ S] (c : ℤ) (y : S) :
    c ∣ Algebra.norm ℤ (1 + algebraMap ℤ S c * y) - 1 := by
  classical
  set b := Module.Free.chooseBasis ℤ S
  rw [Algebra.norm_eq_matrix_det b, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem,
    map_sub, RingHom.map_det, map_one, sub_eq_zero]
  have hc : (Ideal.Quotient.mk (Ideal.span {c})) c = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c)
  have h0 : (Ideal.Quotient.mk (Ideal.span {c})).mapMatrix
      (algebraMap ℤ (Matrix (Module.Free.ChooseBasisIndex ℤ S) (Module.Free.ChooseBasisIndex ℤ S) ℤ) c)
        = 0 := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp [hc]
  rw [map_add, map_one, map_mul, AlgHom.commutes, map_add, map_one, map_mul, h0, zero_mul, add_zero,
    Matrix.det_one]

/- English proof (translation)
Introduce `S _ _ hfree hfin c π y hπ`. Apply the tactic sequence `have hfree' : @Module.Free ℤ S _ _ Algebra.toModule := by convert hfree <;> first | rfl | exact Subsingleton.elim _ _`. Apply the tactic sequence `have hfin' : @Module.Finite ℤ S _ _ Algebra.toModule := by convert hfin <;> first | rfl | exact Subsingleton.elim _ _`. Establish `key` using `@norm_one_add_mul S _ _ hfree' hfin' c y`. Establish `h : c • y = algebraMap ℤ S c * y` using `by first`.

Consider the case `exact Algebra.smul_def c y`. Consider the case `rw [zsmul_eq_mul, eq_intCast]`. Rewrite using `[hπ, h]`. Conclude with `key`.
-/
theorem norm_congruent_one : NormCongrOne := by
  intro S _ _ hfree hfin c π y hπ
  have hfree' : @Module.Free ℤ S _ _ Algebra.toModule := by convert hfree <;> first | rfl | exact Subsingleton.elim _ _
  have hfin' : @Module.Finite ℤ S _ _ Algebra.toModule := by convert hfin <;> first | rfl | exact Subsingleton.elim _ _
  have key := @norm_one_add_mul S _ _ hfree' hfin' c y
  have h : c • y = algebraMap ℤ S c * y := by
    first
    | exact Algebra.smul_def c y
    | rw [zsmul_eq_mul, eq_intCast]
  rw [hπ, h]
  exact key

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Unfold `primeToPart`. Use `set m := orderOf x with hm`. Establish `hm0 : m ≠ 0` using `hx.orderOf_pos.ne'`. Establish `hmpos : 0 < m` using `hx.orderOf_pos`. Use `set v := m.factorization l with hv`.

Use `set m' := m / l ^ v with hm'`. Establish `hcl : Nat.Coprime l m'` using `Nat.coprime_ordCompl hl hm0`. Establish `hcop' : Nat.Coprime (l ^ v) m'` using `Nat.Coprime.pow_left v hcl`. Establish `hm'pos : 0 < m'` using `Nat.ordCompl_pos l hm0`. Establish `hsplit : l ^ v * m' = m` using `Nat.ordProj_mul_ordCompl_eq_self m l`.

Use `set N := (l ^ v) ^ Nat.totient m' with hN`. Use `set oz := orderOf z with hoz`. Establish `hoz0 : 0 < oz` using `hz.orderOf_pos`. Establish `hcz : Nat.Coprime (l ^ a) oz` using `Nat.Coprime.pow_left a hc`. Establish `hφz : 0 < Nat.totient oz` using `by first`.

Consider the case `exact Nat.totient_pos.2 hoz0`. Consider the case `exact Nat.totient_pos hoz0`. Establish `hφm : 0 < Nat.totient m'` using `by first`. Consider the case `exact Nat.totient_pos.2 hm'pos`. Consider the case `exact Nat.totient_pos hm'pos`.

Use `set j := (l ^ a) ^ Nat.totient oz with hj`. Establish `hjz : j % oz = 1 % oz` using `Nat.ModEq.pow_totient hcz`. Establish `hzj : z ^ j = z`. Rewrite using `[← pow_mod_orderOf z j, ← hoz, hjz, pow_mod_orderOf, pow_one]`. Establish `hjr : j = l ^ a * (l ^ a) ^ (Nat.totient oz - 1)`.

Rewrite using `[hj, ← pow_succ', Nat.sub_add_cancel hφz]`. Establish `hzx : z = x ^ j`. Combine the equalities or inequalities in the displayed calculation. Establish `hxj1 : x ^ (j * oz) = 1` using `by rw [pow_mul, ← hzx, hoz, pow_orderOf_eq_one]`. Establish `hmj : m ∣ j * oz` using `orderOf_dvd_of_pow_eq_one hxj1`.

Establish `hlvj : l ^ v ∣ j` using `(Nat.Coprime.pow_left v hc).dvd_of_dvd_mul_right (dvd_trans ⟨m', hsplit.symm⟩ hmj)`. Establish `hlvN : l ^ v ∣ N` using `dvd_pow_self _ hφm.ne'`. Establish `hj1 : 1 ≤ j` using `Nat.one_le_pow _ _ (pow_pos hl.pos a)`. Take `⟨j0, hj0⟩ : ∃ j0, j = j0 + 1` from `⟨j - 1, by omega⟩`. Take `⟨m0, hm0'⟩ : ∃ m0, m = m0 + 1` from `⟨m - 1, by omega⟩`.

Establish `hA : x ^ (j * l ^ a) = x ^ (l ^ a)` using `by rw [pow_mul, ← hzx, ← h]`. Establish `hB : x ^ (l ^ a) * x ^ (m0 * l ^ a) = 1`. Rewrite using `[← pow_add, show l ^ a + m0 * l ^ a = m * l ^ a by rw [hm0']; ring, pow_mul, hm, pow_orderOf_eq_one, one_pow]`. Establish `hx1 : x ^ (j0 * l ^ a) = 1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hB, mul_one]`. Use `_ = x ^ (j * l ^ a) * x ^ (m0 * l ^ a) := by`. Rewrite using `[← mul_assoc, ← pow_add]`. Use `congr 2`. Rewrite using `[hj0]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = 1 := by rw [hA, hB]`. Establish `hmdvd1 : m ∣ j0 * l ^ a` using `orderOf_dvd_of_pow_eq_one hx1`. Establish `hm'dvd : m' ∣ j0` using `(Nat.Coprime.pow_right a hcl.symm).dvd_of_dvd_mul_right (dvd_trans ⟨l ^ v, by rw [mul_comm]; exact hsplit.symm⟩ hmdvd1)`. Establish `hN1 : N ≡ 1 [MOD m']` using `Nat.ModEq.pow_totient hcop'`.

Establish `hj1' : j ≡ 1 [MOD m']`. Rewrite using `[hj0]`. Use `(Nat.modEq_zero_iff_dvd.2 hm'dvd).add_right 1` as an intermediate fact. Simplify using `using this`. Establish `hNj1 : N ≡ j [MOD m']` using `hN1.trans hj1'.symm`.

Establish `hNj2 : N ≡ j [MOD l ^ v]` using `(Nat.modEq_zero_iff_dvd.2 hlvN).trans (Nat.modEq_zero_iff_dvd.2 hlvj).symm`. Establish `hNj : N ≡ j [MOD m]`. Rewrite using `[← hsplit]`. Conclude with `(Nat.modEq_and_modEq_iff_modEq_mul hcop').1 ⟨hNj2, hNj1⟩`. Rewrite using `[hzx, ← pow_mod_orderOf x N, ← pow_mod_orderOf x j, ← hm]`.

Rewrite using `[show N % m = j % m from hNj]`.
-/
theorem primeToPart_unique {M : Type} [Monoid M] {l : ℕ} (hl : l.Prime) {x z : M}
    (hx : IsOfFinOrder x) (hz : IsOfFinOrder z) (hc : Nat.Coprime l (orderOf z)) {a : ℕ}
    (h : x ^ (l ^ a) = z ^ (l ^ a)) : primeToPart l x = z := by
  unfold primeToPart
  set m := orderOf x with hm
  have hm0 : m ≠ 0 := hx.orderOf_pos.ne'
  have hmpos : 0 < m := hx.orderOf_pos
  set v := m.factorization l with hv
  set m' := m / l ^ v with hm'
  have hcl : Nat.Coprime l m' := Nat.coprime_ordCompl hl hm0
  have hcop' : Nat.Coprime (l ^ v) m' := Nat.Coprime.pow_left v hcl
  have hm'pos : 0 < m' := Nat.ordCompl_pos l hm0
  have hsplit : l ^ v * m' = m := Nat.ordProj_mul_ordCompl_eq_self m l
  set N := (l ^ v) ^ Nat.totient m' with hN
  set oz := orderOf z with hoz
  have hoz0 : 0 < oz := hz.orderOf_pos
  have hcz : Nat.Coprime (l ^ a) oz := Nat.Coprime.pow_left a hc
  have hφz : 0 < Nat.totient oz := by
    first
    | exact Nat.totient_pos.2 hoz0
    | exact Nat.totient_pos hoz0
  have hφm : 0 < Nat.totient m' := by
    first
    | exact Nat.totient_pos.2 hm'pos
    | exact Nat.totient_pos hm'pos
  set j := (l ^ a) ^ Nat.totient oz with hj
  have hjz : j % oz = 1 % oz := Nat.ModEq.pow_totient hcz
  have hzj : z ^ j = z := by
    rw [← pow_mod_orderOf z j, ← hoz, hjz, pow_mod_orderOf, pow_one]
  have hjr : j = l ^ a * (l ^ a) ^ (Nat.totient oz - 1) := by
    rw [hj, ← pow_succ', Nat.sub_add_cancel hφz]
  have hzx : z = x ^ j := by
    calc z = z ^ j := hzj.symm
      _ = x ^ j := by rw [hjr, pow_mul z, ← h, ← pow_mul]
  have hxj1 : x ^ (j * oz) = 1 := by rw [pow_mul, ← hzx, hoz, pow_orderOf_eq_one]
  have hmj : m ∣ j * oz := orderOf_dvd_of_pow_eq_one hxj1
  have hlvj : l ^ v ∣ j :=
    (Nat.Coprime.pow_left v hc).dvd_of_dvd_mul_right (dvd_trans ⟨m', hsplit.symm⟩ hmj)
  have hlvN : l ^ v ∣ N := dvd_pow_self _ hφm.ne'
  have hj1 : 1 ≤ j := Nat.one_le_pow _ _ (pow_pos hl.pos a)
  obtain ⟨j0, hj0⟩ : ∃ j0, j = j0 + 1 := ⟨j - 1, by omega⟩
  obtain ⟨m0, hm0'⟩ : ∃ m0, m = m0 + 1 := ⟨m - 1, by omega⟩
  have hA : x ^ (j * l ^ a) = x ^ (l ^ a) := by rw [pow_mul, ← hzx, ← h]
  have hB : x ^ (l ^ a) * x ^ (m0 * l ^ a) = 1 := by
    rw [← pow_add, show l ^ a + m0 * l ^ a = m * l ^ a by rw [hm0']; ring, pow_mul, hm,
      pow_orderOf_eq_one, one_pow]
  have hx1 : x ^ (j0 * l ^ a) = 1 := by
    calc x ^ (j0 * l ^ a) = x ^ (j0 * l ^ a) * (x ^ (l ^ a) * x ^ (m0 * l ^ a)) := by
          rw [hB, mul_one]
      _ = x ^ (j * l ^ a) * x ^ (m0 * l ^ a) := by
          rw [← mul_assoc, ← pow_add]
          congr 2
          rw [hj0]
          ring
      _ = 1 := by rw [hA, hB]
  have hmdvd1 : m ∣ j0 * l ^ a := orderOf_dvd_of_pow_eq_one hx1
  have hm'dvd : m' ∣ j0 :=
    (Nat.Coprime.pow_right a hcl.symm).dvd_of_dvd_mul_right
      (dvd_trans ⟨l ^ v, by rw [mul_comm]; exact hsplit.symm⟩ hmdvd1)
  have hN1 : N ≡ 1 [MOD m'] := Nat.ModEq.pow_totient hcop'
  have hj1' : j ≡ 1 [MOD m'] := by
    rw [hj0]
    have := (Nat.modEq_zero_iff_dvd.2 hm'dvd).add_right 1
    simpa using this
  have hNj1 : N ≡ j [MOD m'] := hN1.trans hj1'.symm
  have hNj2 : N ≡ j [MOD l ^ v] :=
    (Nat.modEq_zero_iff_dvd.2 hlvN).trans (Nat.modEq_zero_iff_dvd.2 hlvj).symm
  have hNj : N ≡ j [MOD m] := by
    rw [← hsplit]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop').1 ⟨hNj2, hNj1⟩
  rw [hzx, ← pow_mod_orderOf x N, ← pow_mod_orderOf x j, ← hm]
  rw [show N % m = j % m from hNj]

/- English proof (translation)
Establish `hmpos : 0 < orderOf x` using `hx.orderOf_pos`. Establish `hm0 : orderOf x ≠ 0` using `hmpos.ne'`. Establish `hcl : Nat.Coprime l (orderOf x / l ^ (orderOf x).factorization l)` using `Nat.coprime_ordCompl hl hm0`. Establish `hcop'` using `Nat.Coprime.pow_left ((orderOf x).factorization l) hcl`. Establish `hm'pos : 0 < orderOf x / l ^ (orderOf x).factorization l` using `Nat.ordCompl_pos l hm0`.

Establish `hsplit : l ^ (orderOf x).factorization l * (orderOf x / l ^ (orderOf x).factorization l) = orderOf x` using `Nat.ordProj_mul_ordCompl_eq_self _ l`. Establish `hφm : 0 < Nat.totient (orderOf x / l ^ (orderOf x).factorization l)` using `by first`. Consider the case `exact Nat.totient_pos.2 hm'pos`. Consider the case `exact Nat.totient_pos hm'pos`. Establish `hP : primeToPart l x = x ^ ((l ^ (orderOf x).factorization l) ^ Nat.totient (orderOf x / l ^ (orderOf x).factorization l))` using `rfl`.

Use `set v := (orderOf x).factorization l with hv`. Use `set m' := orderOf x / l ^ v with hm'`. Use `set N := (l ^ v) ^ Nat.totient m' with hN`. Establish `hlvN : l ^ v ∣ N` using `dvd_pow_self _ hφm.ne'`. Establish `ha : (primeToPart l x) ^ (l ^ v) = x ^ (l ^ v)`.

Rewrite using `[hP, ← pow_mul, ← pow_mod_orderOf x (N * l ^ v), ← pow_mod_orderOf x (l ^ v)]`. Use `congr 1`. Establish `h1 : N * l ^ v ≡ 1 * l ^ v [MOD m']` using `(Nat.ModEq.pow_totient hcop').mul_right _`. Rewrite `h1` using `[one_mul]`. Establish `h2 : N * l ^ v ≡ l ^ v [MOD l ^ v]` using `(Nat.modEq_zero_iff_dvd.2 (dvd_mul_left _ _)).trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl).symm`.

Establish `h3` using `(Nat.modEq_and_modEq_iff_modEq_mul hcop').1 ⟨h2, h1⟩`. Rewrite `h3` using `[hsplit]`. Conclude with `h3`. Establish `hb : Nat.Coprime l (orderOf (primeToPart l x))`. Establish `h4 : (primeToPart l x) ^ m' = 1`.

Rewrite using `[hP, ← pow_mul]`. Take `⟨c, hc⟩` from `hlvN`. Establish `h5 : N * m' = c * orderOf x` using `by rw [hc, ← hsplit]; ring`. Rewrite using `[h5, pow_mul', pow_orderOf_eq_one, one_pow]`. Conclude with `Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one h4) hcl`.

Establish `hc : IsOfFinOrder (primeToPart l x)`. Rewrite using `[hP]`. Conclude with `hx.pow`. Use `⟨ha, hb, hc, fun b hvb => ?_⟩` and prove the remaining obligations. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hvb`.

Rewrite using `[pow_add, pow_mul, pow_mul, ha]`.
-/
private theorem ptp_lemma {M : Type} [Monoid M] {l : ℕ} (hl : l.Prime) {x : M}
    (hx : IsOfFinOrder x) :
    (primeToPart l x) ^ (l ^ (orderOf x).factorization l) = x ^ (l ^ (orderOf x).factorization l) ∧
    Nat.Coprime l (orderOf (primeToPart l x)) ∧ IsOfFinOrder (primeToPart l x) ∧
    ∀ b, (orderOf x).factorization l ≤ b → (primeToPart l x) ^ (l ^ b) = x ^ (l ^ b) := by
  have hmpos : 0 < orderOf x := hx.orderOf_pos
  have hm0 : orderOf x ≠ 0 := hmpos.ne'
  have hcl : Nat.Coprime l (orderOf x / l ^ (orderOf x).factorization l) :=
    Nat.coprime_ordCompl hl hm0
  have hcop' := Nat.Coprime.pow_left ((orderOf x).factorization l) hcl
  have hm'pos : 0 < orderOf x / l ^ (orderOf x).factorization l := Nat.ordCompl_pos l hm0
  have hsplit : l ^ (orderOf x).factorization l * (orderOf x / l ^ (orderOf x).factorization l) =
      orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ l
  have hφm : 0 < Nat.totient (orderOf x / l ^ (orderOf x).factorization l) := by
    first
    | exact Nat.totient_pos.2 hm'pos
    | exact Nat.totient_pos hm'pos
  have hP : primeToPart l x = x ^ ((l ^ (orderOf x).factorization l) ^
      Nat.totient (orderOf x / l ^ (orderOf x).factorization l)) := rfl
  set v := (orderOf x).factorization l with hv
  set m' := orderOf x / l ^ v with hm'
  set N := (l ^ v) ^ Nat.totient m' with hN
  have hlvN : l ^ v ∣ N := dvd_pow_self _ hφm.ne'
  have ha : (primeToPart l x) ^ (l ^ v) = x ^ (l ^ v) := by
    rw [hP, ← pow_mul, ← pow_mod_orderOf x (N * l ^ v), ← pow_mod_orderOf x (l ^ v)]
    congr 1
    have h1 : N * l ^ v ≡ 1 * l ^ v [MOD m'] := (Nat.ModEq.pow_totient hcop').mul_right _
    rw [one_mul] at h1
    have h2 : N * l ^ v ≡ l ^ v [MOD l ^ v] :=
      (Nat.modEq_zero_iff_dvd.2 (dvd_mul_left _ _)).trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl).symm
    have h3 := (Nat.modEq_and_modEq_iff_modEq_mul hcop').1 ⟨h2, h1⟩
    rw [hsplit] at h3
    exact h3
  have hb : Nat.Coprime l (orderOf (primeToPart l x)) := by
    have h4 : (primeToPart l x) ^ m' = 1 := by
      rw [hP, ← pow_mul]
      obtain ⟨c, hc⟩ := hlvN
      have h5 : N * m' = c * orderOf x := by rw [hc, ← hsplit]; ring
      rw [h5, pow_mul', pow_orderOf_eq_one, one_pow]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one h4) hcl
  have hc : IsOfFinOrder (primeToPart l x) := by
    rw [hP]
    exact hx.pow
  refine ⟨ha, hb, hc, fun b hvb => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hvb
  rw [pow_add, pow_mul, pow_mul, ha]

/- English proof (translation)
Introduce `M M' _ _ l x y φ hl hx hy`. Take `⟨hxa, hxc, hxf, hxd⟩` from `ptp_lemma hl hx`. Take `⟨hya, hyc, hyf, hyd⟩` from `ptp_lemma hl hy`. Establish `hmap : ∀ w : M, IsOfFinOrder w → IsOfFinOrder (φ w)` using `fun w hw => by`. Take `⟨n, hn, hwn⟩` from `isOfFinOrder_iff_pow_eq_one.1 hw`.

Conclude with `isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, by rw [← map_pow, hwn, map_one]⟩`. Prove the components needed by the constructor for the conclusion. Establish `hxy : IsOfFinOrder (x * y)` using `(Commute.all x y).isOfFinOrder_mul hx hy`. Use `primeToPart_unique (a := max ((orderOf x).factorization l) ((orderOf y).factorization l)) hl hxy ((Commute.all _ _).isOfFinOrder_mul hxf hyf) ?_ ?_` and prove the remaining obligations. Conclude with `Nat.Coprime.coprime_dvd_right ((Commute.all _ _).orderOf_mul_dvd_mul_orderOf) (Nat.Coprime.mul_right hxc hyc)`.

Rewrite using `[mul_pow, mul_pow, hxd _ (le_max_left _ _), hyd _ (le_max_right _ _)]`. Use `(primeToPart_unique (a := (orderOf x).factorization l) hl (hmap x hx) (hmap _ hxf) ?_ ?_).symm` and prove the remaining obligations. Conclude with `Nat.Coprime.coprime_dvd_right (orderOf_map_dvd φ _) hxc`. Rewrite using `[← map_pow, ← map_pow, hxa]`.
-/
theorem prime_to_part_endomorphism : PrimeToPartEndo := by
  intro M M' _ _ l x y φ hl hx hy
  obtain ⟨hxa, hxc, hxf, hxd⟩ := ptp_lemma hl hx
  obtain ⟨hya, hyc, hyf, hyd⟩ := ptp_lemma hl hy
  have hmap : ∀ w : M, IsOfFinOrder w → IsOfFinOrder (φ w) := fun w hw => by
    obtain ⟨n, hn, hwn⟩ := isOfFinOrder_iff_pow_eq_one.1 hw
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, by rw [← map_pow, hwn, map_one]⟩
  constructor
  · have hxy : IsOfFinOrder (x * y) := (Commute.all x y).isOfFinOrder_mul hx hy
    refine primeToPart_unique (a := max ((orderOf x).factorization l) ((orderOf y).factorization l))
      hl hxy ((Commute.all _ _).isOfFinOrder_mul hxf hyf) ?_ ?_
    · exact Nat.Coprime.coprime_dvd_right ((Commute.all _ _).orderOf_mul_dvd_mul_orderOf)
        (Nat.Coprime.mul_right hxc hyc)
    · rw [mul_pow, mul_pow, hxd _ (le_max_left _ _), hyd _ (le_max_right _ _)]
  · refine (primeToPart_unique (a := (orderOf x).factorization l) hl (hmap x hx) (hmap _ hxf) ?_ ?_).symm
    · exact Nat.Coprime.coprime_dvd_right (orderOf_map_dvd φ _) hxc
    · rw [← map_pow, ← map_pow, hxa]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Unfold `BB`. Simplify using `only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]`.
-/
theorem mem_BB_iff (g N l : ℕ) : l ∈ BB g N ↔ l = g ∨ (l < g ^ N + 1 ∧ l.Prime ∧
    ∃ d ∈ Finset.Icc 1 N, g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))) := by
  unfold BB
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]

/- English proof (translation)
Introduce `g N l hg hl hlg`. Rewrite using `[mem_BB_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h d hd`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Apply `h` to reduce the goal to its premises. Use `right`. Use `⟨?_, hl, d, hd, hc⟩` and prove the remaining obligations. Establish `hd1 : 1 ≤ d` using `(Finset.mem_Icc.mp hd).1`.

Establish `hdN : d ≤ N` using `(Finset.mem_Icc.mp hd).2`. Establish `hgd : 2 ≤ g ^ d` using `le_trans hg (Nat.le_self_pow (by omega) g)`. Break down `Nat.eq_zero_or_pos (padicValNat l (g ^ d - 1)) with h0 | h0` into its components or cases. Rewrite `hc` using `[h0, mul_zero, pow_zero]`. Use linear arithmetic over natural numbers and integers.

Establish `hdvd : l ∣ g ^ d - 1` using `dvd_of_one_le_padicValNat h0`. Establish `hle : l ≤ g ^ d - 1` using `Nat.le_of_dvd (by omega) hdvd`. Establish `hpow : g ^ d ≤ g ^ N` using `Nat.pow_le_pow_right (by omega) hdN`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `h (rfl | ⟨-, -, d, hd, hlt⟩)`.

Conclude with `hlg rfl`. Conclude with `absurd (h d hd) (not_le.mpr hlt)`.
-/
theorem not_mem_bad_primes_iff : NotMemBBIff := by
  intro g N l hg hl hlg
  rw [mem_BB_iff]
  constructor
  · intro h d hd
    by_contra hc
    push_neg at hc
    apply h
    right
    refine ⟨?_, hl, d, hd, hc⟩
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
    have hgd : 2 ≤ g ^ d := le_trans hg (Nat.le_self_pow (by omega) g)
    rcases Nat.eq_zero_or_pos (padicValNat l (g ^ d - 1)) with h0 | h0
    · rw [h0, mul_zero, pow_zero] at hc
      omega
    have hdvd : l ∣ g ^ d - 1 := dvd_of_one_le_padicValNat h0
    have hle : l ≤ g ^ d - 1 := Nat.le_of_dvd (by omega) hdvd
    have hpow : g ^ d ≤ g ^ N := Nat.pow_le_pow_right (by omega) hdN
    omega
  · rintro h (rfl | ⟨-, -, d, hd, hlt⟩)
    · exact hlg rfl
    · exact absurd (h d hd) (not_le.mpr hlt)

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `N a h0 hN`. Use `le_trans ?_ (prodMaxInvLeSq N a h0 hN)` and prove the remaining obligations. Apply `Nat.mul_le_mul_left` to reduce the goal to its premises. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `σ hσ`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢`. Take `⟨A, hA, hc⟩` from `Formalism.GaloisIrreducibility.permSubSumInv (Fin N) σ a hσ`. Conclude with `⟨A, hc, hA⟩`.
-/
theorem subsum_bound : LemmaPSubSum := by
  intro N a h0 hN
  classical
  refine le_trans ?_ (prodMaxInvLeSq N a h0 hN)
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro σ hσ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  obtain ⟨A, hA, hc⟩ := Formalism.GaloisIrreducibility.permSubSumInv (Fin N) σ a hσ
  exact ⟨A, hc, hA⟩

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `K G _ _ _ e`. Rewrite using `[LinearMap.trace_eq_matrix_trace K (MonoidAlgebra.basis G K)]`. Establish `hrep : ∀ (x : MonoidAlgebra K G) (g : G), (MonoidAlgebra.basis G K).repr x g = x.coeff g`. Introduce `x g`. Use `first`.

Consider the case `rfl`. Consider the case `simp [MonoidAlgebra.basis]`. Simplify using `only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply, LinearMap.mulLeft_apply, hrep, MonoidAlgebra.coeff_mul_single_apply, mul_inv_cancel, mul_one]`. Simplify using the standard rewrite rules.
-/
theorem trace_form_regular : TraceRegular := by
  intro K G _ _ _ e
  classical
  rw [LinearMap.trace_eq_matrix_trace K (MonoidAlgebra.basis G K)]
  have hrep : ∀ (x : MonoidAlgebra K G) (g : G), (MonoidAlgebra.basis G K).repr x g = x.coeff g := by
    intro x g
    first
    | rfl
    | simp [MonoidAlgebra.basis]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply,
    LinearMap.mulLeft_apply, hrep, MonoidAlgebra.coeff_mul_single_apply, mul_inv_cancel, mul_one]
  simp

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twistedIdem_def {G : Type} [Group G] [Fintype G] (J : Subgroup G) (χ : J →* ℂˣ) :
    twistedIdem J χ =
      ∑ u : J, ((Nat.card J : ℂ)⁻¹ * (((χ u)⁻¹ : ℂˣ) : ℂ)) • MonoidAlgebra.of ℂ G (u : G) := rfl

open Classical in
/- English proof (translation)
Unfold `twistedIdem`. Rewrite using `[Finset.mul_sum, Finset.smul_sum]`. Use `conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft v)]`. Use `Finset.sum_congr rfl (fun u _ => ?_)` and prove the remaining obligations. Rewrite using `[mul_smul_comm, ← map_mul, smul_smul]`.

Use `congr 1`. Establish `h1` using `(χ v).ne_zero`. Establish `h2` using `(χ u).ne_zero`. Simplify using `only [Equiv.coe_mulLeft, map_mul, mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]`. Apply the tactic sequence `field_simp <;> ring`.
-/
theorem of_mul_twistedIdem {G : Type} [Group G] [Fintype G] (J : Subgroup G) (χ : J →* ℂˣ)
    (v : J) : MonoidAlgebra.of ℂ G (v : G) * twistedIdem J χ
      = ((χ v : ℂˣ) : ℂ) • twistedIdem J χ := by
  classical
  unfold twistedIdem
  rw [Finset.mul_sum, Finset.smul_sum]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft v)]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [mul_smul_comm, ← map_mul, smul_smul]
  congr 1
  have h1 := (χ v).ne_zero
  have h2 := (χ u).ne_zero
  simp only [Equiv.coe_mulLeft, map_mul, mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp <;> ring

open Classical in
/- English proof (translation)
Establish `h0 : (Nat.card J : ℂ) ≠ 0` using `by exact_mod_cast (Nat.card_pos (α := J)).ne'`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl (fun u _ => ?_)` and prove the remaining obligations. Rewrite using `[mul_assoc, Units.inv_mul, mul_one]`. Use `_ = 1 := by`.

Rewrite using `[Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul, mul_inv_cancel₀ h0]`.
-/
theorem sum_coef_twisted {G : Type} [Group G] [Fintype G] (J : Subgroup G) (χ : J →* ℂˣ) :
    ∑ u : J, ((Nat.card J : ℂ)⁻¹ * (((χ u)⁻¹ : ℂˣ) : ℂ)) * ((χ u : ℂˣ) : ℂ) = 1 := by
  have h0 : (Nat.card J : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := J)).ne'
  calc ∑ u : J, ((Nat.card J : ℂ)⁻¹ * (((χ u)⁻¹ : ℂˣ) : ℂ)) * ((χ u : ℂˣ) : ℂ)
      = ∑ _u : J, (Nat.card J : ℂ)⁻¹ := by
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [mul_assoc, Units.inv_mul, mul_one]
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul,
          mul_inv_cancel₀ h0]

open Classical in
/- English proof (translation)
Unfold `twistedIdem`. Rewrite using `[MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]`. Use `Finset.sum_congr rfl (fun u _ => ?_)` and prove the remaining obligations. Simplify using `only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul]`.
-/
theorem twistedIdem_coeff {G : Type} [Group G] [Fintype G] (J : Subgroup G) (χ : J →* ℂˣ)
    (g : G) : (twistedIdem J χ).coeff g =
      ∑ u : J, ((Nat.card J : ℂ)⁻¹ * (((χ u)⁻¹ : ℂˣ) : ℂ)) * (if (u : G) = g then 1 else 0) := by
  classical
  unfold twistedIdem
  rw [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, MonoidAlgebra.of_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul]

/- English proof (translation)
Take `⟨n, hn, hpow⟩` from `(isOfFinOrder_of_finite u).exists_pow_eq_one`. Establish `h1 : ((χ u : ℂˣ) : ℂ) ^ n = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, hpow, map_one, Units.val_one]`. Establish `hnorm : ‖((χ u : ℂˣ) : ℂ)‖ = 1` using `Complex.norm_eq_one_of_pow_eq_one h1 hn.ne'`. Establish `hc : (starRingEnd ℂ) ((χ u : ℂˣ) : ℂ) * ((χ u : ℂˣ) : ℂ) = 1`.

Rewrite using `[Complex.conj_mul', hnorm]`. Simplify using the standard rewrite rules. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀]`. Conclude with `inv_eq_of_mul_eq_one_right hc`.
-/
theorem conj_char_inv {J : Type} [Group J] [Finite J] (χ : J →* ℂˣ) (u : J) :
    (starRingEnd ℂ) (((χ u)⁻¹ : ℂˣ) : ℂ) = ((χ u : ℂˣ) : ℂ) := by
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_of_finite u).exists_pow_eq_one
  have h1 : ((χ u : ℂˣ) : ℂ) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hpow, map_one, Units.val_one]
  have hnorm : ‖((χ u : ℂˣ) : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h1 hn.ne'
  have hc : (starRingEnd ℂ) ((χ u : ℂˣ) : ℂ) * ((χ u : ℂˣ) : ℂ) = 1 := by
    rw [Complex.conj_mul', hnorm]
    simp
  rw [Units.val_inv_eq_inv_val, map_inv₀]
  exact inv_eq_of_mul_eq_one_right hc

open Classical in
/- English proof (translation)
Simplify using `[twistedIdem, map_sum, Representation.asAlgebraHom_of]`.
-/
theorem asAlgebraHom_twistedIdem {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (J : Subgroup G) (χ : J →* ℂˣ) (ρ : Representation ℂ G V) (x : V) :
    ρ.asAlgebraHom (twistedIdem J χ) x =
      ∑ u : J, ((Nat.card J : ℂ)⁻¹ * (((χ u)⁻¹ : ℂˣ) : ℂ)) • ρ (u : G) x := by
  simp [twistedIdem, map_sum, Representation.asAlgebraHom_of]

open Classical in
/- English proof (translation)
Introduce `G _ _ J χ`. Establish `tw_lemma : ∀ g : G, (twistedIdem J χ).coeff g = if h : g ∈ J then (Nat.card J : ℂ)⁻¹ * (((χ ⟨g, h⟩)⁻¹ : ℂˣ) : ℂ) else 0`. Introduce `g`. Rewrite using `[twistedIdem_coeff]`. Use `split_ifs with h`.

Rewrite using `[Finset.sum_eq_single ⟨g, h⟩]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Establish `: (b : G) ≠ g` using `fun e => hb (Subtype.ext e)`. Simplify using `[this]`.

Simplify using the standard rewrite rules. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `u _`. Establish `: (u : G) ≠ g` using `fun e => h (e ▸ u.2)`. Simplify using `[this]`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `nth_rw 1 [twistedIdem_def]`. Rewrite using `[Finset.sum_mul]`. Repeatedly rewrite using `[smul_mul_assoc, of_mul_twistedIdem, smul_smul]`. Rewrite using `[← Finset.sum_smul, sum_coef_twisted, one_smul]`.

Introduce `g`. Rewrite using `[tw_lemma, tw_lemma]`. Distinguish the cases in `hg : g ∈ J`. Establish `hg' : g⁻¹ ∈ J` using `J.inv_mem hg`. Rewrite using `[dif_pos hg', dif_pos hg, map_mul, conj_char_inv]`.

Establish `e : (⟨g⁻¹, hg'⟩ : J) = (⟨g, hg⟩ : J)⁻¹` using `rfl`. Rewrite using `[e, map_inv, inv_inv]`. Simplify using the standard rewrite rules. Establish `hg' : g⁻¹ ∉ J` using `fun h => hg (by simpa using J.inv_mem h)`. Rewrite using `[dif_neg hg', dif_neg hg, map_zero]`.

Rewrite using `[tw_lemma, dif_pos J.one_mem]`. Establish `e : (⟨1, J.one_mem⟩ : J) = 1` using `rfl`. Rewrite using `[e, map_one, inv_one, Units.val_one, mul_one]`. Introduce `V _ _ ρ`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩ u show ρ (u : G) (ρ.asAlgebraHom (twistedIdem J χ) y) = ((χ u : ℂˣ) : ℂ) • ρ.asAlgebraHom (twistedIdem J χ) y`. Rewrite using `[← Representation.asAlgebraHom_of]`. Express the relevant statement in the definitionally equal form `(ρ.asAlgebraHom (MonoidAlgebra.of ℂ G (u : G)) * ρ.asAlgebraHom (twistedIdem J χ)) y = _`. Rewrite using `[← map_mul, of_mul_twistedIdem, map_smul]`.

Both sides reduce to the same expression. Introduce `hx`. Use `⟨x, ?_⟩` and prove the remaining obligations. Rewrite using `[asAlgebraHom_twistedIdem]`. Establish `hx' : ∀ u : J, ρ (u : G) x = ((χ u : ℂˣ) : ℂ) • x` using `hx`.

Repeatedly rewrite using `[hx', smul_smul]`. Rewrite using `[← Finset.sum_smul, sum_coef_twisted, one_smul]`.
-/
theorem twisted_idempotent_holds : TwistedIdempotent := by
  intro G _ _ J χ
  classical
  have tw_lemma : ∀ g : G, (twistedIdem J χ).coeff g =
      if h : g ∈ J then (Nat.card J : ℂ)⁻¹ * (((χ ⟨g, h⟩)⁻¹ : ℂˣ) : ℂ) else 0 := by
    intro g
    rw [twistedIdem_coeff]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨g, h⟩]
      · simp
      · intro b _ hb
        have : (b : G) ≠ g := fun e => hb (Subtype.ext e)
        simp [this]
      · simp
    · apply Finset.sum_eq_zero
      intro u _
      have : (u : G) ≠ g := fun e => h (e ▸ u.2)
      simp [this]
  refine ⟨?_, ?_, ?_, ?_⟩
  · nth_rw 1 [twistedIdem_def]
    rw [Finset.sum_mul]
    simp_rw [smul_mul_assoc, of_mul_twistedIdem, smul_smul]
    rw [← Finset.sum_smul, sum_coef_twisted, one_smul]
  · intro g
    rw [tw_lemma, tw_lemma]
    by_cases hg : g ∈ J
    · have hg' : g⁻¹ ∈ J := J.inv_mem hg
      rw [dif_pos hg', dif_pos hg, map_mul, conj_char_inv]
      have e : (⟨g⁻¹, hg'⟩ : J) = (⟨g, hg⟩ : J)⁻¹ := rfl
      rw [e, map_inv, inv_inv]
      simp
    · have hg' : g⁻¹ ∉ J := fun h => hg (by simpa using J.inv_mem h)
      rw [dif_neg hg', dif_neg hg, map_zero]
  · rw [tw_lemma, dif_pos J.one_mem]
    have e : (⟨1, J.one_mem⟩ : J) = 1 := rfl
    rw [e, map_one, inv_one, Units.val_one, mul_one]
  · intro V _ _ ρ
    ext x
    constructor
    · rintro ⟨y, rfl⟩ u
      show ρ (u : G) (ρ.asAlgebraHom (twistedIdem J χ) y) =
        ((χ u : ℂˣ) : ℂ) • ρ.asAlgebraHom (twistedIdem J χ) y
      rw [← Representation.asAlgebraHom_of]
      change (ρ.asAlgebraHom (MonoidAlgebra.of ℂ G (u : G)) * ρ.asAlgebraHom (twistedIdem J χ)) y = _
      rw [← map_mul, of_mul_twistedIdem, map_smul]
      rfl
    · intro hx
      refine ⟨x, ?_⟩
      rw [asAlgebraHom_twistedIdem]
      have hx' : ∀ u : J, ρ (u : G) x = ((χ u : ℂˣ) : ℂ) • x := hx
      simp_rw [hx', smul_smul]
      rw [← Finset.sum_smul, sum_coef_twisted, one_smul]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Proceed by induction on `e using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add f g hf hg`. Rewrite using `[map_add, map_add, hf, hg, ← Finset.sum_add_distrib]`. Simplify using `[MonoidAlgebra.coeff_add, add_mul]`.

Consider the case `single g r`. Rewrite using `[Representation.asAlgebraHom_single, map_smul, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_single g]`. Simplify using `[Representation.character, MonoidAlgebra.coeff_single]`. Introduce `b _ hb`.

Simplify using `[MonoidAlgebra.coeff_single, Finsupp.single_apply, hb, Ne.symm hb]`. Simplify using the standard rewrite rules.
-/
theorem trace_asAlgebraHom {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (e : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom e) = ∑ h, e.coeff h * ρ.character h := by
  classical
  induction e using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, map_add, hf, hg, ← Finset.sum_add_distrib]
    simp [MonoidAlgebra.coeff_add, add_mul]
  | single g r =>
    rw [Representation.asAlgebraHom_single, map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single g]
    · simp [Representation.character, MonoidAlgebra.coeff_single]
    · intro b _ hb
      simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, hb, Ne.symm hb]
    · simp

/- English proof (translation)
Rewrite using `[MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, Finset.sum_eq_single x]`. Simplify using `[MonoidAlgebra.coeff_smul, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single]`. Introduce `b _ hb`. Simplify using `[MonoidAlgebra.coeff_smul, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, hb]`. Simplify using the standard rewrite rules.
-/
private theorem cip_lemma {G : Type} [Group G] [Fintype G] (c : G → ℂ) (x : G) :
    (∑ y, c y • MonoidAlgebra.of ℂ G y).coeff x = c x := by
  classical
  rw [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, Finset.sum_eq_single x]
  · simp [MonoidAlgebra.coeff_smul, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single]
  · intro b _ hb
    simp [MonoidAlgebra.coeff_smul, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, hb]
  · simp

/- English proof (translation)
Introduce `G V _ _ _ _ _ ρ e he`. Establish `hz : ∀ h : G, (centralIdem ρ).coeff h = (Module.finrank ℂ V : ℂ) / Fintype.card G * ρ.character h⁻¹`. Introduce `h`. Unfold `centralIdem`. Rewrite using `[cip_lemma]`.

Rewrite using `[MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (fun i => by simp)]`. Simplify using `only [mul_one, hz, inv_inv]`. Establish `htr` using `trace_asAlgebraHom ρ e`. Use `set f := ρ.asAlgebraHom e with hf`. Establish `hff : f * f = f` using `by rw [hf, ← map_mul, he]`.

Establish `hproj : LinearMap.IsProj (LinearMap.range f) f` using `⟨fun x => LinearMap.mem_range_self f x, fun x hx => by`. Take `⟨y, rfl⟩` from `hx`. Conclude with `congrArg (fun g : Module.End ℂ V => g y) hff⟩`. Rewrite `htr` using `[hproj.trace]`. Establish `hs : ∑ h, e.coeff h * ((Module.finrank ℂ V : ℂ) / Fintype.card G * ρ.character h) = (Module.finrank ℂ V : ℂ) / Fintype.card G * ∑ h, e.coeff h * ρ.character h`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun h _ => by ring)` and prove the remaining obligations. Rewrite using `[hs, ← htr]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weight_formula : WeightFormula := by
  intro G V _ _ _ _ _ ρ e he
  classical
  have hz : ∀ h : G, (centralIdem ρ).coeff h =
      (Module.finrank ℂ V : ℂ) / Fintype.card G * ρ.character h⁻¹ := by
    intro h
    unfold centralIdem
    rw [cip_lemma]
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp only [mul_one, hz, inv_inv]
  have htr := trace_asAlgebraHom ρ e
  set f := ρ.asAlgebraHom e with hf
  have hff : f * f = f := by rw [hf, ← map_mul, he]
  have hproj : LinearMap.IsProj (LinearMap.range f) f :=
    ⟨fun x => LinearMap.mem_range_self f x, fun x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact congrArg (fun g : Module.End ℂ V => g y) hff⟩
  rw [hproj.trace] at htr
  have hs : ∑ h, e.coeff h * ((Module.finrank ℂ V : ℂ) / Fintype.card G * ρ.character h) =
      (Module.finrank ℂ V : ℂ) / Fintype.card G * ∑ h, e.coeff h * ρ.character h := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun h _ => by ring)
  rw [hs, ← htr]
  ring

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `G V _ _ _ _ _ ρ J χ`. Take `⟨hidem, -, hc1, hrange⟩` from `twisted_idempotent_holds G J χ`. Rewrite using `[weight_formula G V ρ _ hidem, hc1, hrange V ρ, div_inv_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weight_L1_bound : WeightOfTwistedIdempotent := by
  intro G V _ _ _ _ _ ρ J χ
  obtain ⟨hidem, -, hc1, hrange⟩ := twisted_idempotent_holds G J χ
  rw [weight_formula G V ρ _ hidem, hc1, hrange V ρ, div_inv_eq_mul]
  ring

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `G H V W _ _ _ _ _ _ _ _ _ _ ρ σ g h`. Unfold `centralIdem`. Rewrite using `[cip_lemma, cip_lemma, cip_lemma, Representation.char_tensor]`. Establish `e3 : Module.finrank ℂ (TensorProduct ℂ V W) = Module.finrank ℂ V * Module.finrank ℂ W` using `Module.finrank_tensorProduct`. Rewrite using `[e3, Fintype.card_prod]`.

Use `show ((Module.finrank ℂ V * Module.finrank ℂ W : ℕ) : ℂ) / ((Fintype.card G * Fintype.card H : ℕ) : ℂ) * (ρ.character g⁻¹ * σ.character h⁻¹) = (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ρ.character g⁻¹ * ((Module.finrank ℂ W : ℂ) / (Fintype.card H : ℂ) * σ.character h⁻¹)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem central_idempotent_product : CentralIdemProduct := by
  intro G H V W _ _ _ _ _ _ _ _ _ _ ρ σ g h
  unfold centralIdem
  rw [cip_lemma, cip_lemma, cip_lemma, Representation.char_tensor]
  have e3 : Module.finrank ℂ (TensorProduct ℂ V W) = Module.finrank ℂ V * Module.finrank ℂ W :=
    Module.finrank_tensorProduct
  rw [e3, Fintype.card_prod]
  show ((Module.finrank ℂ V * Module.finrank ℂ W : ℕ) : ℂ) / ((Fintype.card G * Fintype.card H : ℕ) : ℂ) *
      (ρ.character g⁻¹ * σ.character h⁻¹) =
    (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * ρ.character g⁻¹ *
      ((Module.finrank ℂ W : ℂ) / (Fintype.card H : ℂ) * σ.character h⁻¹)
  push_cast
  ring

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `K _ _ N`. Rewrite using `[Matrix.card_GL_field]`. Use `set q := Fintype.card K`. Establish `e1 : ∀ i : Fin N, q ^ N - q ^ (i : ℕ) = q ^ (i : ℕ) * (q ^ (N - i) - 1)`. Introduce `i`.

Establish `hi : (i : ℕ) ≤ N` using `i.isLt.le`. Rewrite using `[Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le hi]`. Rewrite using `[Finset.prod_congr rfl (fun i _ => e1 i), Finset.prod_mul_distrib]`. Use `congr 1`. Rewrite using `[Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]`.

Rewrite using `[Fin.prod_univ_eq_prod_range (fun i => q ^ (N - i) - 1) N]`. Establish `e2 : Finset.Icc 1 N = (Finset.range N).image (fun i => N - i)`. Use extensionality with `j`. Simplify using `only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨N - j, by omega, by omega⟩`. Introduce and unpack `⟨i, hi, rfl⟩`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e2, Finset.prod_image (fun a ha b hb h => by simp at ha hb h; omega)]`.
-/
theorem GL_cardinality_split : GLCardSplit := by
  intro K _ _ N
  rw [Matrix.card_GL_field]
  set q := Fintype.card K
  have e1 : ∀ i : Fin N, q ^ N - q ^ (i : ℕ) = q ^ (i : ℕ) * (q ^ (N - i) - 1) := by
    intro i
    have hi : (i : ℕ) ≤ N := i.isLt.le
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le hi]
  rw [Finset.prod_congr rfl (fun i _ => e1 i), Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]
  · rw [Fin.prod_univ_eq_prod_range (fun i => q ^ (N - i) - 1) N]
    have e2 : Finset.Icc 1 N = (Finset.range N).image (fun i => N - i) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨N - j, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        omega
    rw [e2, Finset.prod_image (fun a ha b hb h => by simp at ha hb h; omega)]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `K _ _ d hd`. Use `set F := (Finset.univ : Finset (Fin d → K)).filter (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0) with hF`. Establish `hq : 1 < Nat.card K` using `Finite.one_lt_card`. Establish `hpos : 0 < (Nat.card K) ^ d - 1`. Establish `: 1 < (Nat.card K) ^ d` using `Nat.one_lt_pow (by omega) hq`.

Use linear arithmetic over natural numbers and integers. Establish `hdvd : ∏ c ∈ F, monicOf c ∣ (X ^ (Nat.card K) ^ d - X : K[X])`. Apply `Finset.prod_dvd_of_coprime` to reduce the goal to its premises. Introduce `a ha b hb hab`. Establish `hia : Irreducible (monicOf a)` using `(Finset.mem_filter.mp ha).2.1`.

Establish `hib : Irreducible (monicOf b)` using `(Finset.mem_filter.mp hb).2.1`. Rewrite using `[Function.onFun, hia.coprime_iff_not_dvd]`. Introduce `h`. Conclude with `hab (monicOf_injective (eq_of_monic_of_associated (monicOf_monic a) (monicOf_monic b) (hia.associated_of_dvd hib h)))`. Introduce `c hc`.

Conclude with `((Finset.mem_filter.mp hc).2.1.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X).mp (by rw [monicOf_natDegree])`. Establish `hsplit : (X ^ (Nat.card K) ^ d - X : K[X]) = X * (X ^ ((Nat.card K) ^ d - 1) - C 1)`. Rewrite using `[mul_sub, ← pow_succ', Nat.sub_add_cancel (by omega), C_1, mul_one]`. Establish `hcop : IsCoprime (∏ c ∈ F, monicOf c) (X : K[X])`. Apply `IsCoprime.prod_left` to reduce the goal to its premises.

Introduce `c hc`. Establish `hic : Irreducible (monicOf c)` using `(Finset.mem_filter.mp hc).2.1`. Rewrite using `[hic.coprime_iff_not_dvd]`. Introduce `h`. Establish `h1 : (X : K[X]) ∣ monicOf c` using `(hic.associated_of_dvd irreducible_X h).symm.dvd`.

Conclude with `(Finset.mem_filter.mp hc).2.2 (X_dvd_iff.mp h1)`. Rewrite `hdvd` using `[hsplit]`. Establish `hdvd2` using `hcop.dvd_of_dvd_mul_left hdvd`. Establish `hdeg` using `natDegree_le_of_dvd hdvd2 (X_pow_sub_C_ne_zero hpos 1)`. Rewrite `hdeg` using `[natDegree_prod_of_monic _ _ (fun c _ => monicOf_monic c), natDegree_X_pow_sub_C]`.

Simplify using `only [monicOf_natDegree, Finset.sum_const, smul_eq_mul, Nat.card_eq_fintype_card] at hdeg`. Rewrite using `[mul_comm]`. Conclude with `hdeg`.
-/
theorem irreducible_count_upper_unit : IrredCountUpperUnit := by
  classical
  intro K _ _ d hd
  set F := (Finset.univ : Finset (Fin d → K)).filter
    (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0) with hF
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hpos : 0 < (Nat.card K) ^ d - 1 := by
    have : 1 < (Nat.card K) ^ d := Nat.one_lt_pow (by omega) hq
    omega
  have hdvd : ∏ c ∈ F, monicOf c ∣ (X ^ (Nat.card K) ^ d - X : K[X]) := by
    apply Finset.prod_dvd_of_coprime
    · intro a ha b hb hab
      have hia : Irreducible (monicOf a) := (Finset.mem_filter.mp ha).2.1
      have hib : Irreducible (monicOf b) := (Finset.mem_filter.mp hb).2.1
      rw [Function.onFun, hia.coprime_iff_not_dvd]
      intro h
      exact hab (monicOf_injective (eq_of_monic_of_associated (monicOf_monic a) (monicOf_monic b)
        (hia.associated_of_dvd hib h)))
    · intro c hc
      exact ((Finset.mem_filter.mp hc).2.1.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X).mp
        (by rw [monicOf_natDegree])
  have hsplit : (X ^ (Nat.card K) ^ d - X : K[X]) = X * (X ^ ((Nat.card K) ^ d - 1) - C 1) := by
    rw [mul_sub, ← pow_succ', Nat.sub_add_cancel (by omega), C_1, mul_one]
  have hcop : IsCoprime (∏ c ∈ F, monicOf c) (X : K[X]) := by
    apply IsCoprime.prod_left
    intro c hc
    have hic : Irreducible (monicOf c) := (Finset.mem_filter.mp hc).2.1
    rw [hic.coprime_iff_not_dvd]
    intro h
    have h1 : (X : K[X]) ∣ monicOf c := (hic.associated_of_dvd irreducible_X h).symm.dvd
    exact (Finset.mem_filter.mp hc).2.2 (X_dvd_iff.mp h1)
  rw [hsplit] at hdvd
  have hdvd2 := hcop.dvd_of_dvd_mul_left hdvd
  have hdeg := natDegree_le_of_dvd hdvd2 (X_pow_sub_C_ne_zero hpos 1)
  rw [natDegree_prod_of_monic _ _ (fun c _ => monicOf_monic c), natDegree_X_pow_sub_C] at hdeg
  simp only [monicOf_natDegree, Finset.sum_const, smul_eq_mul, Nat.card_eq_fintype_card] at hdeg
  rw [mul_comm]
  exact hdeg

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open UniqueFactorizationMonoid in
/- English proof (translation)
Unfold `degType`. Establish `h0 : (0 : K[X]) ∉ UniqueFactorizationMonoid.normalizedFactors f` using `fun h => (UniqueFactorizationMonoid.prime_of_normalized_factor 0 h).ne_zero rfl`. Rewrite using `[← Polynomial.natDegree_multiset_prod _ h0]`. Conclude with `Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated (UniqueFactorizationMonoid.prod_normalizedFactors hf))`.
-/
theorem sum_degType {K : Type} [Field K] (f : K[X]) (hf : f ≠ 0) :
    (degType f).sum = f.natDegree := by
  classical
  unfold degType
  have h0 : (0 : K[X]) ∉ UniqueFactorizationMonoid.normalizedFactors f := fun h =>
    (UniqueFactorizationMonoid.prime_of_normalized_factor 0 h).ne_zero rfl
  rw [← Polynomial.natDegree_multiset_prod _ h0]
  exact Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_eq_degree_of_associated (UniqueFactorizationMonoid.prod_normalizedFactors hf))

/- English proof (translation)
Unfold `sqWeight degType`. Rewrite using `[Multiset.map_map]`. Both sides reduce to the same expression.
-/
theorem sqWeight_eq {K : Type} [Field K] [Fintype K] (f : K[X]) :
    sqWeight f = ((degType f).map (fun d => ((Fintype.card K : ℝ) ^ d - 1)⁻¹)).prod := by
  unfold sqWeight degType
  rw [Multiset.map_map]
  rfl

/- English proof (translation)
Unfold `degType at hd`. Take `⟨P, hP, rfl⟩` from `Multiset.mem_map.mp hd`. Establish `hirr` using `UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP`. Conclude with `Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hirr)`.
-/
theorem one_le_of_mem_degType {K : Type} [Field K] (f : K[X]) (d : ℕ) (hd : d ∈ degType f) :
    1 ≤ d := by
  classical
  unfold degType at hd
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hd
  have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP
  exact Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hirr)

/- English proof (translation)
Establish `hq0 : 0 < q` using `by linarith`. Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Establish `ha : 1 ≤ a` using `hs a (Multiset.mem_cons_self a s)`.

Establish `ih'` using `ih (fun d hd => hs d (Multiset.mem_cons_of_mem hd))`. Rewrite using `[Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons, pow_add, mul_inv]`. Establish `hqa : 1 < q ^ a` using `one_lt_pow₀ hq (by omega)`. Establish `h1 : (q ^ a)⁻¹ ≤ (q ^ a - 1)⁻¹` using `inv_anti₀ (by linarith) (by linarith)`. Establish `h2 : 0 ≤ (q ^ s.sum)⁻¹` using `(inv_pos.mpr (pow_pos hq0 _)).le`.

Establish `h3 : 0 ≤ (q ^ a - 1)⁻¹` using `(inv_pos.mpr (by linarith)).le`. Conclude with `mul_le_mul h1 ih' h2 h3`.
-/
theorem inv_pow_sum_le (q : ℝ) (hq : 1 < q) (s : Multiset ℕ) (hs : ∀ d ∈ s, 1 ≤ d) :
    (q ^ s.sum)⁻¹ ≤ (s.map (fun d => (q ^ d - 1)⁻¹)).prod := by
  have hq0 : 0 < q := by linarith
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : 1 ≤ a := hs a (Multiset.mem_cons_self a s)
    have ih' := ih (fun d hd => hs d (Multiset.mem_cons_of_mem hd))
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons, pow_add, mul_inv]
    have hqa : 1 < q ^ a := one_lt_pow₀ hq (by omega)
    have h1 : (q ^ a)⁻¹ ≤ (q ^ a - 1)⁻¹ := inv_anti₀ (by linarith) (by linarith)
    have h2 : 0 ≤ (q ^ s.sum)⁻¹ := (inv_pos.mpr (pow_pos hq0 _)).le
    have h3 : 0 ≤ (q ^ a - 1)⁻¹ := (inv_pos.mpr (by linarith)).le
    exact mul_le_mul h1 ih' h2 h3

/- English proof (translation)
Introduce `K _ _ N hN`. Establish `hq : (1 : ℝ) < (Fintype.card K : ℝ)` using `by exact_mod_cast Fintype.one_lt_card`. Establish `hw : ∀ c ∈ sqSet K N, ((Fintype.card K : ℝ) ^ N)⁻¹ ≤ sqWeight (monicOf c)`. Introduce `c _`. Rewrite using `[sqWeight_eq]`.

Establish `h` using `inv_pow_sum_le _ hq (degType (monicOf c)) (one_le_of_mem_degType _)`. Rewrite `h` using `[sum_degType _ (monicOf_monic c).ne_zero, monicOf_natDegree]`. Then use the resulting hypothesis. Establish `h1 : ((sqSet K N).card : ℝ) * ((Fintype.card K : ℝ) ^ N)⁻¹ ≤ ∑ c ∈ sqSet K N, sqWeight (monicOf c)`. Rewrite using `[← nsmul_eq_mul]`. Conclude with `Finset.card_nsmul_le_sum _ _ _ hw`.

Establish `h2 : Fintype.card K ^ N ≤ (sqSet K N).card + 2 * Fintype.card K ^ (N - 1)` using `squarefree_count K N hN`. Establish `h3 : (Fintype.card K : ℝ) ^ N ≤ ((sqSet K N).card : ℝ) + 2 * (Fintype.card K : ℝ) ^ (N - 1)`. Conclude with `h2` after adjusting the coercions. Use `le_trans ?_ h1` and prove the remaining obligations. Establish `hpos : (0 : ℝ) < (Fintype.card K : ℝ) ^ N` using `by positivity`.

Establish `h5 : (Fintype.card K : ℝ) ^ N = (Fintype.card K : ℝ) ^ (N - 1) * (Fintype.card K : ℝ)`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hN]`. Rewrite using `[← div_eq_mul_inv, le_div_iff₀ hpos]`. Establish `h6 : (2 / (Fintype.card K : ℝ)) * (Fintype.card K : ℝ) ^ N = 2 * (Fintype.card K : ℝ) ^ (N - 1)`. Rewrite using `[h5]`.

Clear the denominators using the available nonvanishing facts. Use polynomial arithmetic with `[h3, h6]`.
-/
theorem square_mass_lower_bound : SqMassLower := by
  intro K _ _ N hN
  have hq : (1 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.one_lt_card
  have hw : ∀ c ∈ sqSet K N, ((Fintype.card K : ℝ) ^ N)⁻¹ ≤ sqWeight (monicOf c) := by
    intro c _
    rw [sqWeight_eq]
    have h := inv_pow_sum_le _ hq (degType (monicOf c)) (one_le_of_mem_degType _)
    rwa [sum_degType _ (monicOf_monic c).ne_zero, monicOf_natDegree] at h
  have h1 : ((sqSet K N).card : ℝ) * ((Fintype.card K : ℝ) ^ N)⁻¹ ≤
      ∑ c ∈ sqSet K N, sqWeight (monicOf c) := by
    rw [← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ hw
  have h2 : Fintype.card K ^ N ≤ (sqSet K N).card + 2 * Fintype.card K ^ (N - 1) :=
    squarefree_count K N hN
  have h3 : (Fintype.card K : ℝ) ^ N ≤ ((sqSet K N).card : ℝ) + 2 * (Fintype.card K : ℝ) ^ (N - 1) := by
    exact_mod_cast h2
  refine le_trans ?_ h1
  have hpos : (0 : ℝ) < (Fintype.card K : ℝ) ^ N := by positivity
  have h5 : (Fintype.card K : ℝ) ^ N = (Fintype.card K : ℝ) ^ (N - 1) * (Fintype.card K : ℝ) := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  have h6 : (2 / (Fintype.card K : ℝ)) * (Fintype.card K : ℝ) ^ N
      = 2 * (Fintype.card K : ℝ) ^ (N - 1) := by
    rw [h5]; field_simp
  nlinarith [h3, h6]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Simplify using `[sqSet]`.
-/
theorem mem_sqSet {K : Type} [Field K] [Fintype K] {N : ℕ} (c : Fin N → K) :
    c ∈ sqSet K N ↔ Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 := by
  simp [sqSet]

/- English proof (translation)
Introduce `K _ _ N n hn`. Use `set q : ℝ := (Fintype.card K : ℝ) with hq`. Establish `hconst : ∀ c : Fin N → K, (∀ d ∈ Finset.Icc 1 N, (degType (monicOf c)).count d = n d) → sqWeight (monicOf c) = ∏ d ∈ Finset.Icc 1 N, ((q ^ d - 1)⁻¹) ^ (n d)`. Introduce `c hcount`. Rewrite using `[sqWeight_eq, Finset.prod_multiset_map_count]`.

Establish `hsub : (degType (monicOf c)).toFinset ⊆ Finset.Icc 1 N`. Introduce `d hd`. Establish `hd'` using `Multiset.mem_toFinset.mp hd`. Use `Finset.mem_Icc.mpr ⟨one_le_of_mem_degType _ d hd', ?_⟩` and prove the remaining obligations. Establish `h1` using `Multiset.le_sum_of_mem hd'`.

Rewrite `h1` using `[sum_degType _ (monicOf_monic c).ne_zero, monicOf_natDegree]`. Then use the resulting hypothesis. Rewrite using `[Finset.prod_subset hsub]`. Conclude with `Finset.prod_congr rfl fun d hd => by rw [hcount d hd]`. Introduce `d _ hd`. Rewrite using `[Multiset.count_eq_zero_of_notMem (fun h => hd (Multiset.mem_toFinset.mpr h)), pow_zero]`.

Use `(Finset.sum_congr rfl (fun c hc => by` and prove the remaining obligations. Simplify using `only [Finset.mem_filter] at hc`. Conclude with `hconst c hc.2)).trans ?_`. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Establish `hcard` using `type_count_exact K N n hn`.

Establish `key : ∀ a : ℕ → ℕ, (∏ d ∈ Finset.Icc 1 N, ((a d : ℕ) : ℝ) / (q ^ d - 1) ^ (n d)) = ((∏ d ∈ Finset.Icc 1 N, a d : ℕ) : ℝ) * ∏ d ∈ Finset.Icc 1 N, ((q ^ d - 1)⁻¹) ^ (n d)`. Introduce `a`. Rewrite using `[Nat.cast_prod, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun d _ => by rw [inv_pow, div_eq_mul_inv]`. Rewrite using `[key, ← hcard]`.

Use `congr 3`. Use extensionality with `c`. Simplify using `only [Finset.mem_filter, mem_sqSet, Finset.mem_univ, true_and, and_assoc]`. Both sides reduce to the same expression.
-/
theorem type_weight_exact : TypeWeightExact := by
  intro K _ _ N n hn
  set q : ℝ := (Fintype.card K : ℝ) with hq
  have hconst : ∀ c : Fin N → K,
      (∀ d ∈ Finset.Icc 1 N, (degType (monicOf c)).count d = n d) →
      sqWeight (monicOf c) = ∏ d ∈ Finset.Icc 1 N, ((q ^ d - 1)⁻¹) ^ (n d) := by
    intro c hcount
    rw [sqWeight_eq, Finset.prod_multiset_map_count]
    have hsub : (degType (monicOf c)).toFinset ⊆ Finset.Icc 1 N := by
      intro d hd
      have hd' := Multiset.mem_toFinset.mp hd
      refine Finset.mem_Icc.mpr ⟨one_le_of_mem_degType _ d hd', ?_⟩
      have h1 := Multiset.le_sum_of_mem hd'
      rwa [sum_degType _ (monicOf_monic c).ne_zero, monicOf_natDegree] at h1
    rw [Finset.prod_subset hsub]
    · exact Finset.prod_congr rfl fun d hd => by rw [hcount d hd]
    · intro d _ hd
      rw [Multiset.count_eq_zero_of_notMem (fun h => hd (Multiset.mem_toFinset.mpr h)), pow_zero]
  refine (Finset.sum_congr rfl (fun c hc => by
    simp only [Finset.mem_filter] at hc
    exact hconst c hc.2)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := type_count_exact K N n hn
  have key : ∀ a : ℕ → ℕ, (∏ d ∈ Finset.Icc 1 N, ((a d : ℕ) : ℝ) / (q ^ d - 1) ^ (n d)) =
      ((∏ d ∈ Finset.Icc 1 N, a d : ℕ) : ℝ) * ∏ d ∈ Finset.Icc 1 N, ((q ^ d - 1)⁻¹) ^ (n d) := by
    intro a
    rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun d _ => by rw [inv_pow, div_eq_mul_inv]
  rw [key, ← hcard]
  congr 3
  ext c
  simp only [Finset.mem_filter, mem_sqSet, Finset.mem_univ, true_and, and_assoc]
  rfl

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `G _ _ _ e he hstar`. Use `set M : Matrix G G ℂ := Matrix.of fun x y : G => e.coeff (x⁻¹ * y) with hM`. Establish `hH : M.conjTranspose = M`. Use extensionality with `x y`. Simplify using `only [hM, Matrix.conjTranspose_apply, Matrix.of_apply]`.

Rewrite using `[show x⁻¹ * y = (y⁻¹ * x)⁻¹ by group, hstar]`. Both sides reduce to the same expression. Establish `hsq : M * M = M`. Use extensionality with `x y`. Simplify using `only [hM, Matrix.mul_apply, Matrix.of_apply]`.

Establish `h1` using `congrArg (fun f : MonoidAlgebra ℂ G => f.coeff (x⁻¹ * y)) he`. Rewrite using `[← h1, MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (fun i => by simp)]`. Conclude with `Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ (fun z => by`. Simplify using `only [Equiv.coe_mulLeft]`. Use `congr 2`.

Use the proof step `group)`. Establish `hM2 : M = M.conjTranspose * M` using `by rw [hH, hsq]`. Rewrite using `[hM2]`. Conclude with `Matrix.posSemidef_conjTranspose_mul_self M`.
-/
theorem idempotent_positive_type : IdempotentPositiveType := by
  intro G _ _ _ e he hstar
  classical
  set M : Matrix G G ℂ := Matrix.of fun x y : G => e.coeff (x⁻¹ * y) with hM
  have hH : M.conjTranspose = M := by
    ext x y
    simp only [hM, Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [show x⁻¹ * y = (y⁻¹ * x)⁻¹ by group, hstar]
    rfl
  have hsq : M * M = M := by
    ext x y
    simp only [hM, Matrix.mul_apply, Matrix.of_apply]
    have h1 := congrArg (fun f : MonoidAlgebra ℂ G => f.coeff (x⁻¹ * y)) he
    rw [← h1, MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (fun i => by simp)]
    exact Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ (fun z => by
      simp only [Equiv.coe_mulLeft]
      congr 2
      group)
  have hM2 : M = M.conjTranspose * M := by rw [hH, hsq]
  rw [hM2]
  exact Matrix.posSemidef_conjTranspose_mul_self M

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Module in
/- English proof (translation)
Use `set p := LinearMap.charpoly s with hp`. Establish `hspl : p.Splits` using `IsAlgClosed.splits p`. Establish `hcard : p.roots.card = p.natDegree` using `Polynomial.splits_iff_card_roots.1 hspl`. Establish `hdeg : p.natDegree = Module.finrank ℂ V` using `LinearMap.charpoly_natDegree s`. Establish `hsum : p.roots.sum = (Module.finrank ℂ V : ℂ)`.

Rewrite using `[← htr, Module.End.trace_eq_sum_roots_charpoly_of_splits hspl]`. Establish `hroot : ∀ μ ∈ p.roots, μ ^ m = 1`. Introduce `μ hμ`. Establish `hr : p.IsRoot μ` using `(Polynomial.mem_roots (LinearMap.charpoly_monic s).ne_zero).1 hμ`. Establish `hev : s.HasEigenvalue μ` using `(Module.End.hasEigenvalue_iff_isRoot_charpoly s μ).2 hr`.

Take `⟨v, hv⟩` from `hev.exists_hasEigenvector`. Establish `h1` using `hv.pow_apply m`. Rewrite `h1` using `[hsm]`. Express the relevant statement in the definitionally equal form `v = μ ^ m • v at h1`. Establish `hv0 : v ≠ 0` using `hv.2`.

Establish `h2 : (μ ^ m - 1) • v = 0` using `by rw [sub_smul, ← h1, one_smul, sub_self]`. Break down `smul_eq_zero.1 h2 with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h`. Conclude with `absurd h hv0`. Establish `hnorm : ∀ μ ∈ p.roots, ‖μ‖ = 1`.

Introduce `μ hμ`. Establish `h2 : ‖μ‖ ^ m = 1` using `by rw [← norm_pow, hroot μ hμ, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h2`. Establish `hre_le : ∀ μ ∈ p.roots, μ.re ≤ 1` using `fun μ hμ => (Complex.re_le_norm μ).trans (hnorm μ hμ).le`. Establish `hresum : ∀ t : Multiset ℂ, t.sum.re = (t.map Complex.re).sum`.

Introduce `t`. Proceed by induction on `t using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a t ih => simp [ih]`. Establish `hsumre : (p.roots.map Complex.re).sum = Module.finrank ℂ V`.

Rewrite using `[← hresum, hsum]`. Simplify using the standard rewrite rules. Establish `hall : ∀ μ ∈ p.roots, μ = 1`. Introduce `μ hμ`. Establish `hμ'` using `hμ`.

Take `⟨t, ht⟩` from `Multiset.exists_cons_of_mem hμ`. Establish `hle : (t.map Complex.re).sum ≤ t.card`. Establish `h3` using `Multiset.sum_map_le_sum_map (s := t) (f := Complex.re) (g := fun _ => (1 : ℝ)) (fun x hx => hre_le x (by rw [ht]; exact Multiset.mem_cons_of_mem hx))`. Simplify using `using h3`. Establish `hc : t.card + 1 = Module.finrank ℂ V`.

Rewrite using `[← hdeg, ← hcard, ht, Multiset.card_cons]`. Rewrite `hsumre` using `[ht, Multiset.map_cons, Multiset.sum_cons]`. Establish `hre1 : μ.re = 1`. Establish `h4` using `hre_le μ hμ'`. Establish `h5 : ((t.card + 1 : ℕ) : ℝ) = (Module.finrank ℂ V : ℝ)` using `by exact_mod_cast hc`.

Move the coercions through the operations in `at h5`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn1` using `hnorm μ hμ'`. Establish `h6 : μ.im = 0`. Establish `h7 : ‖μ‖ ^ 2 = μ.re * μ.re + μ.im * μ.im`.

Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Rewrite `h7` using `[hn1, hre1]`. Use polynomial arithmetic with `[sq_nonneg μ.im]`. Conclude with `Complex.ext (by simp [hre1]) (by simp [h6])`. Establish `hroots : p.roots = Multiset.replicate (Module.finrank ℂ V) 1` using `Multiset.eq_replicate.2 ⟨by rw [hcard, hdeg], hall⟩`.

Establish `hpoly : p = (X - C (1 : ℂ)) ^ Module.finrank ℂ V`. Establish `h8` using `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard`. Rewrite `h8` using `[(LinearMap.charpoly_monic s).leadingCoeff, C_1, one_mul, hroots, Multiset.map_replicate, Multiset.prod_replicate]`. Conclude with `h8.symm`. Establish `hae : Polynomial.aeval s ((X - C (1 : ℂ)) ^ Module.finrank ℂ V) = 0`.

Rewrite using `[← hpoly]`. Conclude with `LinearMap.aeval_self_charpoly s`. Establish `hmin1 : minpoly ℂ s ∣ (X - C (1 : ℂ)) ^ Module.finrank ℂ V` using `minpoly.dvd ℂ s hae`. Establish `hmin2 : minpoly ℂ s ∣ X ^ m - C (1 : ℂ)` using `minpoly.dvd ℂ s (by simp [hsm])`. Establish `hsep : (minpoly ℂ s).Separable` using `(Polynomial.separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast hm.ne') one_ne_zero).of_dvd hmin2`.

Take `⟨i, -, hassoc⟩` from `(dvd_prime_pow (Polynomial.prime_X_sub_C (1 : ℂ)) _).1 hmin1`. Establish `hint : IsIntegral ℂ s` using `IsIntegral.of_finite ℂ s`. Establish `heq : minpoly ℂ s = (X - C (1 : ℂ)) ^ i` using `Polynomial.eq_of_monic_of_associated (minpoly.monic hint) ((monic_X_sub_C 1).pow i) hassoc`. Establish `hi1 : i ≤ 1`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `hsq` using `hsep.squarefree`. Rewrite `hsq` using `[heq]`. Establish `h9 : (X - C (1 : ℂ)) * (X - C (1 : ℂ)) ∣ (X - C (1 : ℂ)) ^ i`. Rewrite using `[← pow_two]`.

Conclude with `pow_dvd_pow _ hcon`. Conclude with `(Polynomial.prime_X_sub_C (1 : ℂ)).not_unit (hsq _ h9)`. Establish `hae2` using `minpoly.aeval ℂ s`. Rewrite `hae2` using `[heq]`. Use `interval_cases i`.

Establish `h10 : (1 : Module.End ℂ V) = 0` using `by simpa using hae2 haveI := subsingleton_of_zero_eq_one h10.symm`. Conclude with `Subsingleton.elim _ _`. Simplify `hae2` using `[sub_eq_zero]`.
-/
theorem end_eq_one_of_trace {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (s : Module.End ℂ V) (m : ℕ) (hm : 0 < m) (hsm : s ^ m = 1)
    (htr : LinearMap.trace ℂ V s = (Module.finrank ℂ V : ℂ)) : s = 1 := by
  classical
  set p := LinearMap.charpoly s with hp
  have hspl : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.card = p.natDegree := Polynomial.splits_iff_card_roots.1 hspl
  have hdeg : p.natDegree = Module.finrank ℂ V := LinearMap.charpoly_natDegree s
  have hsum : p.roots.sum = (Module.finrank ℂ V : ℂ) := by
    rw [← htr, Module.End.trace_eq_sum_roots_charpoly_of_splits hspl]
  have hroot : ∀ μ ∈ p.roots, μ ^ m = 1 := by
    intro μ hμ
    have hr : p.IsRoot μ := (Polynomial.mem_roots (LinearMap.charpoly_monic s).ne_zero).1 hμ
    have hev : s.HasEigenvalue μ := (Module.End.hasEigenvalue_iff_isRoot_charpoly s μ).2 hr
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have h1 := hv.pow_apply m
    rw [hsm] at h1
    change v = μ ^ m • v at h1
    have hv0 : v ≠ 0 := hv.2
    have h2 : (μ ^ m - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv0
  have hnorm : ∀ μ ∈ p.roots, ‖μ‖ = 1 := by
    intro μ hμ
    have h2 : ‖μ‖ ^ m = 1 := by rw [← norm_pow, hroot μ hμ, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h2
  have hre_le : ∀ μ ∈ p.roots, μ.re ≤ 1 := fun μ hμ =>
    (Complex.re_le_norm μ).trans (hnorm μ hμ).le
  have hresum : ∀ t : Multiset ℂ, t.sum.re = (t.map Complex.re).sum := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simp
    | cons a t ih => simp [ih]
  have hsumre : (p.roots.map Complex.re).sum = Module.finrank ℂ V := by
    rw [← hresum, hsum]
    simp
  have hall : ∀ μ ∈ p.roots, μ = 1 := by
    intro μ hμ
    have hμ' := hμ
    obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hμ
    have hle : (t.map Complex.re).sum ≤ t.card := by
      have h3 := Multiset.sum_map_le_sum_map (s := t) (f := Complex.re) (g := fun _ => (1 : ℝ))
        (fun x hx => hre_le x (by rw [ht]; exact Multiset.mem_cons_of_mem hx))
      simpa using h3
    have hc : t.card + 1 = Module.finrank ℂ V := by
      rw [← hdeg, ← hcard, ht, Multiset.card_cons]
    rw [ht, Multiset.map_cons, Multiset.sum_cons] at hsumre
    have hre1 : μ.re = 1 := by
      have h4 := hre_le μ hμ'
      have h5 : ((t.card + 1 : ℕ) : ℝ) = (Module.finrank ℂ V : ℝ) := by exact_mod_cast hc
      push_cast at h5
      linarith
    have hn1 := hnorm μ hμ'
    have h6 : μ.im = 0 := by
      have h7 : ‖μ‖ ^ 2 = μ.re * μ.re + μ.im * μ.im := by
        rw [Complex.sq_norm, Complex.normSq_apply]
      rw [hn1, hre1] at h7
      nlinarith [sq_nonneg μ.im]
    exact Complex.ext (by simp [hre1]) (by simp [h6])
  have hroots : p.roots = Multiset.replicate (Module.finrank ℂ V) 1 :=
    Multiset.eq_replicate.2 ⟨by rw [hcard, hdeg], hall⟩
  have hpoly : p = (X - C (1 : ℂ)) ^ Module.finrank ℂ V := by
    have h8 := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
    rw [(LinearMap.charpoly_monic s).leadingCoeff, C_1, one_mul, hroots, Multiset.map_replicate,
      Multiset.prod_replicate] at h8
    exact h8.symm
  have hae : Polynomial.aeval s ((X - C (1 : ℂ)) ^ Module.finrank ℂ V) = 0 := by
    rw [← hpoly]
    exact LinearMap.aeval_self_charpoly s
  have hmin1 : minpoly ℂ s ∣ (X - C (1 : ℂ)) ^ Module.finrank ℂ V := minpoly.dvd ℂ s hae
  have hmin2 : minpoly ℂ s ∣ X ^ m - C (1 : ℂ) := minpoly.dvd ℂ s (by simp [hsm])
  have hsep : (minpoly ℂ s).Separable :=
    (Polynomial.separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast hm.ne') one_ne_zero).of_dvd hmin2
  obtain ⟨i, -, hassoc⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C (1 : ℂ)) _).1 hmin1
  have hint : IsIntegral ℂ s := IsIntegral.of_finite ℂ s
  have heq : minpoly ℂ s = (X - C (1 : ℂ)) ^ i :=
    Polynomial.eq_of_monic_of_associated (minpoly.monic hint) ((monic_X_sub_C 1).pow i) hassoc
  have hi1 : i ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsq := hsep.squarefree
    rw [heq] at hsq
    have h9 : (X - C (1 : ℂ)) * (X - C (1 : ℂ)) ∣ (X - C (1 : ℂ)) ^ i := by
      rw [← pow_two]
      exact pow_dvd_pow _ hcon
    exact (Polynomial.prime_X_sub_C (1 : ℂ)).not_unit (hsq _ h9)
  have hae2 := minpoly.aeval ℂ s
  rw [heq] at hae2
  interval_cases i
  · have h10 : (1 : Module.End ℂ V) = 0 := by simpa using hae2
    haveI := subsingleton_of_zero_eq_one h10.symm
    exact Subsingleton.elim _ _
  · simpa [sub_eq_zero] using hae2

/- English proof (translation)
Introduce `K _ φ n m γ hm hγ htr`. Use `set γ' : Matrix (Fin n) (Fin n) ℂ := γ.map φ with hγ'`. Establish `h1 : γ' ^ m = 1`. Rewrite using `[hγ', ← Matrix.map_pow, hγ, Matrix.map_one φ (map_zero φ) (map_one φ)]`. Establish `h2 : γ'.trace = (n : ℂ)`.

Establish `: γ'.trace = φ γ.trace` using `by simp [Matrix.trace, hγ', map_sum]`. Rewrite using `[this, htr, map_natCast]`. Establish `hs : (Matrix.toLinAlgEquiv' γ') ^ m = 1` using `by rw [← map_pow, h1, map_one]`. Establish `hts : LinearMap.trace ℂ (Fin n → ℂ) (Matrix.toLinAlgEquiv' γ') = (Module.finrank ℂ (Fin n → ℂ) : ℂ)`. Rewrite using `[Module.finrank_fin_fun]`.

Conclude with `(Matrix.trace_toLin'_eq γ').trans h2`. Establish `h3` using `end_eq_one_of_trace _ m hm hs hts`. Establish `h4 : γ' = 1`. Use `congrArg (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).symm h3` as an intermediate fact. Simplify using `using this`.

Apply `Matrix.map_injective φ.injective` to reduce the goal to its premises. Use `show γ.map φ = (1 : Matrix (Fin n) (Fin n) K).map φ`. Rewrite using `[← hγ', h4, Matrix.map_one φ (map_zero φ) (map_one φ)]`.
-/
theorem finite_order_trace_full : FiniteOrderTraceFull := by
  intro K _ φ n m γ hm hγ htr
  classical
  set γ' : Matrix (Fin n) (Fin n) ℂ := γ.map φ with hγ'
  have h1 : γ' ^ m = 1 := by
    rw [hγ', ← Matrix.map_pow, hγ, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have h2 : γ'.trace = (n : ℂ) := by
    have : γ'.trace = φ γ.trace := by simp [Matrix.trace, hγ', map_sum]
    rw [this, htr, map_natCast]
  have hs : (Matrix.toLinAlgEquiv' γ') ^ m = 1 := by rw [← map_pow, h1, map_one]
  have hts : LinearMap.trace ℂ (Fin n → ℂ) (Matrix.toLinAlgEquiv' γ') =
      (Module.finrank ℂ (Fin n → ℂ) : ℂ) := by
    rw [Module.finrank_fin_fun]
    exact (Matrix.trace_toLin'_eq γ').trans h2
  have h3 := end_eq_one_of_trace _ m hm hs hts
  have h4 : γ' = 1 := by
    have := congrArg (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).symm h3
    simpa using this
  apply Matrix.map_injective φ.injective
  show γ.map φ = (1 : Matrix (Fin n) (Fin n) K).map φ
  rw [← hγ', h4, Matrix.map_one φ (map_zero φ) (map_one φ)]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `k V ι _ _ _ _ _ t Φ g b c π hc ht hΦ hπ i`. Establish `hpow : ∀ (n : ℕ) (j : ι), (t ^ n) (b j) = c j ^ n • b j`. Introduce `n j`. Proceed by induction on `n with`. Consider the case `zero => simp`.

Consider the case `succ n ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih, map_smul, ht, smul_smul, ← pow_succ]`. Establish `hw : (t ^ g) (Φ (b i)) = c i • Φ (b i)`. Rewrite using `[← hΦ, ht, map_smul]`. Establish `hcoord : ∀ j, (b.coord j) ∘ₗ (t ^ g) = c j ^ g • b.coord j`.

Introduce `j`. Apply `b.ext` to reduce the goal to its premises. Introduce `k`. Simplify using `only [LinearMap.comp_apply, hpow, map_smul, LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs with h <;> simp [h]`.

Establish `hj : ∀ j, j ≠ π i → b.coord j (Φ (b i)) = 0`. Introduce `j hj`. Establish `e1` using `LinearMap.congr_fun (hcoord j) (Φ (b i))`. Rewrite `e1` using `[LinearMap.comp_apply, hw, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]`. Establish `hne : c j ^ g ≠ c i`.

Introduce `h`. Apply `hj` to reduce the goal to its premises. Establish `h2` using `hπ (π.symm j)`. Rewrite `h2` using `[Equiv.apply_symm_apply]`. Rewrite `h` using `[h2]`.

Establish `h3` using `hc h`. Rewrite using `[← h3, Equiv.apply_symm_apply]`. Establish `h4 : (c i - c j ^ g) * b.coord j (Φ (b i)) = 0` using `by rw [sub_mul, e1, sub_self]`. Break down `mul_eq_zero.mp h4 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h).symm hne`.

Conclude with `h`. Establish `hsum : Φ (b i) = b.repr (Φ (b i)) (π i) • b (π i)` using `by conv_lhs => rw [← b.sum_repr (Φ (b i))]`. Rewrite using `[Finset.sum_eq_single (π i)]`. Introduce `j _ hj'`. Rewrite using `[← Module.Basis.coord_apply, hj j hj', zero_smul]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `⟨b.repr (Φ (b i)) (π i), ?_, hsum⟩` and prove the remaining obligations. Introduce `ha`. Rewrite `hsum` using `[ha, zero_smul]`.

Conclude with `b.ne_zero i (Φ.injective (hsum.trans (map_zero Φ).symm))`.
-/
theorem frobenius_permutes_lines : FrobPermutesLines := by
  intro k V ι _ _ _ _ _ t Φ g b c π hc ht hΦ hπ i
  have hpow : ∀ (n : ℕ) (j : ι), (t ^ n) (b j) = c j ^ n • b j := by
    intro n j
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, ht, smul_smul, ← pow_succ]
  have hw : (t ^ g) (Φ (b i)) = c i • Φ (b i) := by
    rw [← hΦ, ht, map_smul]
  have hcoord : ∀ j, (b.coord j) ∘ₗ (t ^ g) = c j ^ g • b.coord j := by
    intro j
    apply b.ext
    intro k
    simp only [LinearMap.comp_apply, hpow, map_smul, LinearMap.smul_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    split_ifs with h <;> simp [h]
  have hj : ∀ j, j ≠ π i → b.coord j (Φ (b i)) = 0 := by
    intro j hj
    have e1 := LinearMap.congr_fun (hcoord j) (Φ (b i))
    rw [LinearMap.comp_apply, hw, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at e1
    have hne : c j ^ g ≠ c i := by
      intro h
      apply hj
      have h2 := hπ (π.symm j)
      rw [Equiv.apply_symm_apply] at h2
      rw [h2] at h
      have h3 := hc h
      rw [← h3, Equiv.apply_symm_apply]
    have h4 : (c i - c j ^ g) * b.coord j (Φ (b i)) = 0 := by rw [sub_mul, e1, sub_self]
    rcases mul_eq_zero.mp h4 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  have hsum : Φ (b i) = b.repr (Φ (b i)) (π i) • b (π i) := by
    conv_lhs => rw [← b.sum_repr (Φ (b i))]
    rw [Finset.sum_eq_single (π i)]
    · intro j _ hj'
      rw [← Module.Basis.coord_apply, hj j hj', zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine ⟨b.repr (Φ (b i)) (π i), ?_, hsum⟩
  intro ha
  rw [ha, zero_smul] at hsum
  exact b.ne_zero i (Φ.injective (hsum.trans (map_zero Φ).symm))

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial
open scoped ComplexOrder

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `R V _ _ _ MM a eps pr hMM hae hap`. Establish `hcomm : ∀ f : V →ₗ[R] V, a ∘ₗ f = f ∘ₗ a → ∀ y, a (f y) = f (a y)`. Introduce `f hf y`. Use `LinearMap.congr_fun hf y` as an intermediate fact. Simplify using `using this`.

Establish `hrange : ∀ f : V →ₗ[R] V, a ∘ₗ f = f ∘ₗ a → ∀ x ∈ LinearMap.range f, a x ∈ LinearMap.range f`. Introduce `f hf x hx`. Take `⟨y, rfl⟩` from `LinearMap.mem_range.mp hx`. Conclude with `LinearMap.mem_range.mpr ⟨a y, (hcomm f hf y).symm⟩`. Establish `h1 : ∀ x ∈ MM ⊓ LinearMap.range eps, a x ∈ MM ⊓ LinearMap.range eps`.

Introduce `x hx`. Rewrite `hx`, the goal using `[Submodule.mem_inf]`. Conclude with `⟨hMM x hx.1, hrange eps hae x hx.2⟩`. Use `⟨h1, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Rewrite `hx`, the goal using `[Submodule.mem_inf]`. Conclude with `⟨h1 x hx.1, hrange pr hap x hx.2⟩`. Introduce `x hx`. Take `⟨z, hz, rfl⟩` from `Submodule.mem_map.mp hx`. Conclude with `Submodule.mem_map.mpr ⟨a z, h1 z hz, (hcomm pr hap z).symm⟩`.
-/
theorem scope_of_S3_holds : CommutesWithIdempotents := by
  intro R V _ _ _ MM a eps pr hMM hae hap
  have hcomm : ∀ f : V →ₗ[R] V, a ∘ₗ f = f ∘ₗ a → ∀ y, a (f y) = f (a y) := by
    intro f hf y
    have := LinearMap.congr_fun hf y
    simpa using this
  have hrange : ∀ f : V →ₗ[R] V, a ∘ₗ f = f ∘ₗ a →
      ∀ x ∈ LinearMap.range f, a x ∈ LinearMap.range f := by
    intro f hf x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    exact LinearMap.mem_range.mpr ⟨a y, (hcomm f hf y).symm⟩
  have h1 : ∀ x ∈ MM ⊓ LinearMap.range eps, a x ∈ MM ⊓ LinearMap.range eps := by
    intro x hx
    rw [Submodule.mem_inf] at hx ⊢
    exact ⟨hMM x hx.1, hrange eps hae x hx.2⟩
  refine ⟨h1, ?_, ?_⟩
  · intro x hx
    rw [Submodule.mem_inf] at hx ⊢
    exact ⟨h1 x hx.1, hrange pr hap x hx.2⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_map.mpr ⟨a z, h1 z hz, (hcomm pr hap z).symm⟩

/- English proof (translation)
Introduce `R V _ _ _ Mt e pr he hpr x hx`. Rewrite `hx` using `[Submodule.mem_inf, Submodule.mem_inf]`. Take `⟨⟨hxM, hxp⟩, hxe⟩` from `hx`. Take `⟨a, rfl⟩` from `LinearMap.mem_range.mp hxp`. Take `⟨b, hb⟩` from `LinearMap.mem_range.mp hxe`.

Establish `hpx : pr (pr a) = pr a`. Use `LinearMap.congr_fun hpr a` as an intermediate fact. Simplify using `using this`. Establish `hex : e (pr a) = pr a`. Rewrite using `[← hb]`.

Use `LinearMap.congr_fun he b` as an intermediate fact. Simplify using `using this`. Conclude with `Submodule.mem_map.mpr ⟨pr a, Submodule.mem_map.mpr ⟨pr a, hxM, hpx⟩, hex⟩`.
-/
theorem drop_lattice_inclusion : DropLatticeIncl := by
  intro R V _ _ _ Mt e pr he hpr x hx
  rw [Submodule.mem_inf, Submodule.mem_inf] at hx
  obtain ⟨⟨hxM, hxp⟩, hxe⟩ := hx
  obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hxp
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hxe
  have hpx : pr (pr a) = pr a := by
    have := LinearMap.congr_fun hpr a
    simpa using this
  have hex : e (pr a) = pr a := by
    rw [← hb]
    have := LinearMap.congr_fun he b
    simpa using this
  exact Submodule.mem_map.mpr ⟨pr a, Submodule.mem_map.mpr ⟨pr a, hxM, hpx⟩, hex⟩

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Polynomial Formalism.GaloisIrreducibility

/- English proof (translation)
Conclude with `Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt c)`.
-/
theorem monicOf_monic' {K : Type} [Field K] {N : ℕ} (c : Fin N → K) : (monicOf c).Monic := by
  exact Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt c)

/- English proof (translation)
Introduce `K _ _ M`. Simplify `h K M (fun _ => True)` using `[Fintype.card_perm, Nat.factorial_ne_zero]`.
-/
theorem sqMassLeOne_of (h : TypeSetWeight) : SqMassLeOne := by
  intro K _ _ M
  simpa [Fintype.card_perm, Nat.factorial_ne_zero] using h K M (fun _ => True)

/- English proof (translation)
Introduce `K _ _ N a ha haN`. Establish `hfilt : (sqSet K N).filter (fun c => ∃ h : K[X], h ∣ monicOf c ∧ h.natDegree = a) = (sqSet K N).filter (fun c => IsSubSum (degType (monicOf c)) a)`. Apply `Finset.filter_congr` to reduce the goal to its premises. Introduce `c _`. Conclude with `hD K (monicOf c) a (monicOf_monic' c).ne_zero`.

Rewrite using `[hfilt]`. Use `le_trans (h K N (fun m => IsSubSum m a)) ?_` and prove the remaining obligations. Establish `hP'` using `hP N a ha haN`. Establish `hf : (0 : ℝ) < N.factorial` using `by exact_mod_cast Nat.factorial_pos N`. Rewrite using `[div_le_iff₀ hf]`.

Establish `h8 : (8 : ℝ) * (((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => IsSubSum σ.partition.parts a)).card : ℝ) ≤ 7 * N.factorial`. Conclude with `hP'` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem localEstimateIV_of (h : TypeSetWeight) (hP : LemmaPSubSum) (hD : DivisorDegreeSubSum) :
    LocalEstimateIV := by
  intro K _ _ N a ha haN
  classical
  have hfilt : (sqSet K N).filter (fun c => ∃ h : K[X], h ∣ monicOf c ∧ h.natDegree = a) =
      (sqSet K N).filter (fun c => IsSubSum (degType (monicOf c)) a) := by
    apply Finset.filter_congr
    intro c _
    exact hD K (monicOf c) a (monicOf_monic' c).ne_zero
  rw [hfilt]
  refine le_trans (h K N (fun m => IsSubSum m a)) ?_
  have hP' := hP N a ha haN
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [div_le_iff₀ hf]
  have h8 : (8 : ℝ) * (((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun σ => IsSubSum σ.partition.parts a)).card : ℝ) ≤ 7 * N.factorial := by
    exact_mod_cast hP'
  linarith

/- English proof (translation)
Introduce `K _ _ N hN`. Establish `hiff : ∀ f : K[X], f ≠ 0 → ((∃ P : K[X], Irreducible P ∧ P ∣ f ∧ P.natDegree.Prime ∧ N < 2 * P.natDegree ∧ P.natDegree + 3 ≤ N) ↔ ∃ p ∈ degType f, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)`. Introduce `f hf`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨P, hPi, hPd, hp⟩`.

Take `⟨q, hq, hPq⟩` from `UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hf hPi hPd`. Establish `hdeg : P.natDegree = q.natDegree` using `Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hPq)`. Use `⟨q.natDegree, Multiset.mem_map.2 ⟨q, hq, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hdeg]`. Conclude with `hp`.

Introduce and unpack `⟨p, hp, hpp⟩`. Take `⟨q, hq, rfl⟩` from `Multiset.mem_map.1 hp`. Conclude with `⟨q, UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq, UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq, hpp⟩`. Establish `hfilt : (sqSet K N).filter (fun c => ¬ ∃ P : K[X], Irreducible P ∧ P ∣ monicOf c ∧ P.natDegree.Prime ∧ N < 2 * P.natDegree ∧ P.natDegree + 3 ≤ N) = (sqSet K N).filter (fun c => ¬ ∃ p ∈ degType (monicOf c), p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)`. Apply `Finset.filter_congr` to reduce the goal to its premises.

Introduce `c _`. Rewrite using `[hiff _ (monicOf_monic' c).ne_zero]`. Rewrite using `[hfilt]`. Establish `hT` using `h K N (fun m => ¬ ∃ p ∈ m, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)`. Establish `hparts : ∀ σ : Equiv.Perm (Fin N), (∃ p ∈ σ.partition.parts, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) ↔ (∃ p ∈ σ.cycleType, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)`.

Introduce `σ`. Rewrite using `[Equiv.Perm.parts_partition]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, hp, hpp⟩`. Break down `Multiset.mem_add.1 hp with h1 | h1` into its components or cases.

Conclude with `⟨p, h1, hpp⟩`. Rewrite `hpp` using `[Multiset.eq_of_mem_replicate h1]`. Conclude with `absurd hpp.1 Nat.not_prime_one`. Introduce and unpack `⟨p, hp, hpp⟩`. Conclude with `⟨p, Multiset.mem_add.2 (Or.inl hp), hpp⟩`.

Establish `hf : (0 : ℝ) < N.factorial` using `by exact_mod_cast Nat.factorial_pos N`. Establish `hgoal : (((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => ¬ ∃ p ∈ σ.partition.parts, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)).card : ℝ) / N.factorial ≤ 1 - 1 / (5 * Real.log N)`. Rewrite using `[div_le_iff₀ hf]`. Establish `hadd` using `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Equiv.Perm (Fin N)))) (fun σ : Equiv.Perm (Fin N) => ∃ p ∈ σ.partition.parts, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)`. Simplify using `only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hadd`.

Use `beta_reduce at hadd`. Establish `hQ : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∃ p ∈ σ.partition.parts, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) = Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∃ p ∈ σ.cycleType, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N` using `Finset.filter_congr (fun σ _ => hparts σ)`. Rewrite `hadd` using `[hQ]`. Establish `hadd'` using `congrArg (fun n : ℕ => (n : ℝ)) hadd`. Simplify using `only [Nat.cast_add] at hadd'`.

Rewrite `hadd'` using `[hC N]`. Establish `hsum` using `hS N hN`. Establish `hsum' : ∑ p ∈ Finset.range (N + 1) with Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N, (N.factorial : ℝ) / p = N.factorial * ∑ p ∈ Finset.range (N + 1) with Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N, 1 / (p : ℝ)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hadd'` using `[hsum']`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hsum hf.le]`. Conclude with `le_trans (le_of_eq (by congr)) (le_trans hT (le_trans (le_of_eq (by congr)) hgoal))`.
-/
theorem localEstimateV_of (h : TypeSetWeight) (hC : CycleProbSum) (hS : PrimeRecipSum) :
    LocalEstimateV := by
  intro K _ _ N hN
  classical
  have hiff : ∀ f : K[X], f ≠ 0 → ((∃ P : K[X], Irreducible P ∧ P ∣ f ∧ P.natDegree.Prime ∧
      N < 2 * P.natDegree ∧ P.natDegree + 3 ≤ N) ↔
      ∃ p ∈ degType f, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) := by
    intro f hf
    constructor
    · rintro ⟨P, hPi, hPd, hp⟩
      obtain ⟨q, hq, hPq⟩ :=
        UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hf hPi hPd
      have hdeg : P.natDegree = q.natDegree :=
        Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hPq)
      refine ⟨q.natDegree, Multiset.mem_map.2 ⟨q, hq, rfl⟩, ?_⟩
      rw [← hdeg]
      exact hp
    · rintro ⟨p, hp, hpp⟩
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hp
      exact ⟨q, UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq,
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq, hpp⟩
  have hfilt : (sqSet K N).filter (fun c => ¬ ∃ P : K[X], Irreducible P ∧ P ∣ monicOf c ∧
      P.natDegree.Prime ∧ N < 2 * P.natDegree ∧ P.natDegree + 3 ≤ N) =
      (sqSet K N).filter (fun c => ¬ ∃ p ∈ degType (monicOf c), p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) := by
    apply Finset.filter_congr
    intro c _
    rw [hiff _ (monicOf_monic' c).ne_zero]
  rw [hfilt]
  have hT := h K N (fun m => ¬ ∃ p ∈ m, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)
  have hparts : ∀ σ : Equiv.Perm (Fin N), (∃ p ∈ σ.partition.parts, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) ↔
      (∃ p ∈ σ.cycleType, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) := by
    intro σ
    rw [Equiv.Perm.parts_partition]
    constructor
    · rintro ⟨p, hp, hpp⟩
      rcases Multiset.mem_add.1 hp with h1 | h1
      · exact ⟨p, h1, hpp⟩
      · rw [Multiset.eq_of_mem_replicate h1] at hpp
        exact absurd hpp.1 Nat.not_prime_one
    · rintro ⟨p, hp, hpp⟩
      exact ⟨p, Multiset.mem_add.2 (Or.inl hp), hpp⟩
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hgoal : (((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun σ =>
      ¬ ∃ p ∈ σ.partition.parts, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)).card : ℝ) / N.factorial ≤
      1 - 1 / (5 * Real.log N) := by
    rw [div_le_iff₀ hf]
    have hadd := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Equiv.Perm (Fin N))))
      (fun σ : Equiv.Perm (Fin N) => ∃ p ∈ σ.partition.parts, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N)
    simp only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hadd
    beta_reduce at hadd
    have hQ : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
        ∃ p ∈ σ.partition.parts, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) =
        Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
          ∃ p ∈ σ.cycleType, p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N :=
      Finset.filter_congr (fun σ _ => hparts σ)
    rw [hQ] at hadd
    have hadd' := congrArg (fun n : ℕ => (n : ℝ)) hadd
    simp only [Nat.cast_add] at hadd'
    rw [hC N] at hadd'
    have hsum := hS N hN
    have hsum' : ∑ p ∈ Finset.range (N + 1) with Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N,
        (N.factorial : ℝ) / p =
        N.factorial * ∑ p ∈ Finset.range (N + 1) with Nat.Prime p ∧ N < 2 * p ∧ p + 3 ≤ N,
          1 / (p : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      ring
    rw [hsum'] at hadd'
    nlinarith [mul_le_mul_of_nonneg_left hsum hf.le]
  exact le_trans (le_of_eq (by congr)) (le_trans hT (le_trans (le_of_eq (by congr)) hgoal))

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Polynomial

/- English proof (translation)
Introduce `k V _ _ _ _ p₁ p₂ h1 h2 h12`. Establish `hle : LinearMap.range (p₁ + p₂ - p₁ ∘ₗ p₂) ≤ LinearMap.range p₁ ⊔ LinearMap.range p₂`. Introduce `x hx`. Take `⟨y, rfl⟩` from `LinearMap.mem_range.mp hx`. Establish `e : (p₁ + p₂ - p₁ ∘ₗ p₂) y = p₁ (y - p₂ y) + p₂ y`.

Simplify using `only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Submodule.add_mem_sup (LinearMap.mem_range_self p₁ _) (LinearMap.mem_range_self p₂ _)`. Conclude with `(Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)`.
-/
theorem bad_rank_union_bound : BadRankUnion := by
  intro k V _ _ _ _ p₁ p₂ h1 h2 h12
  have hle : LinearMap.range (p₁ + p₂ - p₁ ∘ₗ p₂) ≤ LinearMap.range p₁ ⊔ LinearMap.range p₂ := by
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    have e : (p₁ + p₂ - p₁ ∘ₗ p₂) y = p₁ (y - p₂ y) + p₂ y := by
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_sub]
      abel
    rw [e]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self p₁ _) (LinearMap.mem_range_self p₂ _)
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

/- English proof (translation)
Introduce `k V ι _ _ _ _ _ t c hc hchar`. Establish `hroot : ∀ i, t.HasEigenvalue (c i)`. Introduce `i`. Rewrite using `[Module.End.hasEigenvalue_iff_isRoot_charpoly, hchar, Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff]`. Conclude with `⟨i, Finset.mem_univ _, by simp⟩`.

Use `choose v hv using fun i => (hroot i).exists_hasEigenvector`. Establish `hli : LinearIndependent k v` using `Module.End.eigenvectors_linearIndependent' t c hc v hv`. Establish `hdeg : (∏ i, (X - C (c i))).natDegree = Fintype.card ι`. Rewrite using `[Polynomial.natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (c i))]`. Simplify using the standard rewrite rules.

Establish `hcard : Fintype.card ι = Module.finrank k V`. Rewrite using `[← hdeg, ← hchar, LinearMap.charpoly_natDegree]`. Break down `isEmpty_or_nonempty ι with hι | hι` into its components or cases. Use `haveI : Subsingleton V := Module.finrank_zero_iff.1 (by rw [← hcard]; simp)`. Conclude with `⟨Module.Basis.empty V, fun i => isEmptyElim i⟩`.

Use `⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[coe_basisOfLinearIndependentOfCardEqFinrank]`. Conclude with `(hv i).apply_eq_smul`.
-/
theorem eigenbasis_of_distinct_roots : EigenbasisOfDistinctRoots := by
  intro k V ι _ _ _ _ _ t c hc hchar
  classical
  have hroot : ∀ i, t.HasEigenvalue (c i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hchar, Polynomial.IsRoot,
      Polynomial.eval_prod, Finset.prod_eq_zero_iff]
    exact ⟨i, Finset.mem_univ _, by simp⟩
  choose v hv using fun i => (hroot i).exists_hasEigenvector
  have hli : LinearIndependent k v := Module.End.eigenvectors_linearIndependent' t c hc v hv
  have hdeg : (∏ i, (X - C (c i))).natDegree = Fintype.card ι := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (c i))]
    simp
  have hcard : Fintype.card ι = Module.finrank k V := by
    rw [← hdeg, ← hchar, LinearMap.charpoly_natDegree]
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI : Subsingleton V := Module.finrank_zero_iff.1 (by rw [← hcard]; simp)
    exact ⟨Module.Basis.empty V, fun i => isEmptyElim i⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, fun i => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  exact (hv i).apply_eq_smul

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Establish `hsub : s.toFinset ⊆ Finset.Icc 1 N`. Introduce `d hd`. Rewrite `hd` using `[Multiset.mem_toFinset]`. Establish `h2` using `Multiset.le_sum_of_mem hd`. Rewrite `h2` using `[hs]`.

Conclude with `Finset.mem_Icc.mpr ⟨h d hd, h2⟩`. Rewrite using `[← Finset.sum_subset hsub]`. Use `conv_rhs => rw [← hs]`. Rewrite using `[Finset.sum_multiset_count]`. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations.

Rewrite using `[smul_eq_mul, mul_comm]`. Introduce `d _ hd`. Rewrite `hd` using `[Multiset.mem_toFinset]`. Rewrite using `[Multiset.count_eq_zero.mpr hd, mul_zero]`.
-/
theorem sum_mul_count_eq (s : Multiset ℕ) (N : ℕ) (h : ∀ d ∈ s, 1 ≤ d) (hs : s.sum = N) :
    ∑ d ∈ Finset.Icc 1 N, d * s.count d = N := by
  have hsub : s.toFinset ⊆ Finset.Icc 1 N := by
    intro d hd
    rw [Multiset.mem_toFinset] at hd
    have h2 := Multiset.le_sum_of_mem hd
    rw [hs] at h2
    exact Finset.mem_Icc.mpr ⟨h d hd, h2⟩
  rw [← Finset.sum_subset hsub]
  · conv_rhs => rw [← hs]
    rw [Finset.sum_multiset_count]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [smul_eq_mul, mul_comm]
  · intro d _ hd
    rw [Multiset.mem_toFinset] at hd
    rw [Multiset.count_eq_zero.mpr hd, mul_zero]

/- English proof (translation)
Use extensionality with `d`. Distinguish the cases in `h2 : d ∈ Finset.Icc 2 N`. Conclude with `h d h2`. Distinguish the cases in `h3 : d = 1 ∧ 1 ≤ N`. Take `⟨rfl, hN⟩` from `h3`.

Establish `h1mem : 1 ∈ Finset.Icc 1 N` using `Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩`. Establish `e1` using `Finset.add_sum_erase (Finset.Icc 1 N) (fun d => d * s.count d) h1mem`. Establish `e2` using `Finset.add_sum_erase (Finset.Icc 1 N) (fun d => d * m.count d) h1mem`. Establish `e3 : ∑ x ∈ (Finset.Icc 1 N).erase 1, x * s.count x = ∑ x ∈ (Finset.Icc 1 N).erase 1, x * m.count x`. Use `Finset.sum_congr rfl (fun x hx => ?_)` and prove the remaining obligations.

Take `⟨hne, hx'⟩` from `Finset.mem_erase.mp hx`. Rewrite `hx'` using `[Finset.mem_Icc]`. Rewrite using `[h x (Finset.mem_Icc.mpr ⟨by omega, hx'.2⟩)]`. Use `beta_reduce at e1 e2`. Rewrite `e1` using `[sum_mul_count_eq s N hs1 hs]`.

Rewrite `e2` using `[sum_mul_count_eq m N hm1 hm]`. Simplify using `only [one_mul] at e1 e2`. Use linear arithmetic over natural numbers and integers. Establish `hout : ∀ t : Multiset ℕ, (∀ x ∈ t, 1 ≤ x) → t.sum = N → t.count d = 0`. Introduce `t ht1 hts`.

Rewrite using `[Multiset.count_eq_zero]`. Introduce `hd`. Establish `ha` using `ht1 d hd`. Establish `hb` using `Multiset.le_sum_of_mem hd`. Rewrite `hb` using `[hts]`.

Rewrite `h2` using `[Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hout s hs1 hs, hout m hm1 hm]`.
-/
theorem multiset_eq_of_count (s m : Multiset ℕ) (N : ℕ) (hs1 : ∀ d ∈ s, 1 ≤ d) (hs : s.sum = N)
    (hm1 : ∀ d ∈ m, 1 ≤ d) (hm : m.sum = N)
    (h : ∀ d ∈ Finset.Icc 2 N, s.count d = m.count d) : s = m := by
  ext d
  by_cases h2 : d ∈ Finset.Icc 2 N
  · exact h d h2
  by_cases h3 : d = 1 ∧ 1 ≤ N
  · obtain ⟨rfl, hN⟩ := h3
    have h1mem : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩
    have e1 := Finset.add_sum_erase (Finset.Icc 1 N) (fun d => d * s.count d) h1mem
    have e2 := Finset.add_sum_erase (Finset.Icc 1 N) (fun d => d * m.count d) h1mem
    have e3 : ∑ x ∈ (Finset.Icc 1 N).erase 1, x * s.count x =
        ∑ x ∈ (Finset.Icc 1 N).erase 1, x * m.count x := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      obtain ⟨hne, hx'⟩ := Finset.mem_erase.mp hx
      rw [Finset.mem_Icc] at hx'
      rw [h x (Finset.mem_Icc.mpr ⟨by omega, hx'.2⟩)]
    beta_reduce at e1 e2
    rw [sum_mul_count_eq s N hs1 hs] at e1
    rw [sum_mul_count_eq m N hm1 hm] at e2
    simp only [one_mul] at e1 e2
    omega
  · have hout : ∀ t : Multiset ℕ, (∀ x ∈ t, 1 ≤ x) → t.sum = N → t.count d = 0 := by
      intro t ht1 hts
      rw [Multiset.count_eq_zero]
      intro hd
      have ha := ht1 d hd
      have hb := Multiset.le_sum_of_mem hd
      rw [hts] at hb
      rw [Finset.mem_Icc] at h2
      omega
    rw [hout s hs1 hs, hout m hm1 hm]

/- English proof (translation)
Unfold `sqWeight`. Apply `Multiset.prod_nonneg` to reduce the goal to its premises. Introduce `x hx`. Take `⟨P, -, rfl⟩` from `Multiset.mem_map.mp hx`. Establish `: (1 : ℝ) ≤ (Fintype.card K : ℝ) ^ P.natDegree` using `one_le_pow₀ (by exact_mod_cast Fintype.card_pos)`.

Conclude with `inv_nonneg.mpr (by linarith)`.
-/
theorem sqWeight_nonneg {K : Type} [Field K] [Fintype K] (f : K[X]) : 0 ≤ sqWeight f := by
  unfold sqWeight
  apply Multiset.prod_nonneg
  intro x hx
  obtain ⟨P, -, rfl⟩ := Multiset.mem_map.mp hx
  have : (1 : ℝ) ≤ (Fintype.card K : ℝ) ^ P.natDegree :=
    one_le_pow₀ (by exact_mod_cast Fintype.card_pos)
  exact inv_nonneg.mpr (by linarith)

/- English proof (translation)
Use `set n : ℕ → ℕ := fun d => m.count d with hn`. Establish `hsum : ∑ d ∈ Finset.Icc 1 N, d * n d = N` using `sum_mul_count_eq m N hm1 hm`. Take `⟨S, hS, hSsum⟩ : ∃ S : Finset (Fin N → K), (∀ c ∈ sqSet K N, (∀ d ∈ Finset.Icc 1 N, (degType (monicOf c)).count d = n d) → c ∈ S) ∧ ∑ c ∈ S, sqWeight (monicOf c) = _` from `⟨_, fun c hc h => by simp only [Finset.mem_filter]; exact ⟨hc, h⟩, type_weight_exact K N n hsum⟩`. Take `⟨S', hS', hc⟩ : ∃ S' : Finset (Equiv.Perm (Fin N)), (∀ σ ∈ S', ∀ d ∈ Finset.Icc 2 N, σ.cycleType.count d = n d) ∧ S'.card * ∏ d ∈ Finset.Icc 1 N, (d ^ n d * (n d).factorial) = N.factorial` from `⟨_, fun σ hσ => by`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ`.

Conclude with `hσ,`. Use `cycle_type_probability N n hsum⟩`. Establish `step1 : ∑ c ∈ (sqSet K N).filter (fun c => degType (monicOf c) = m), sqWeight (monicOf c) ≤ ∑ c ∈ S, sqWeight (monicOf c)`. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `c hc`.

Establish `hc'` using `Finset.mem_filter.mp hc`. Conclude with `hS c hc'.1 (fun d _ => by rw [hc'.2])`. Introduce `c _ _`. Conclude with `sqWeight_nonneg _`. Establish `step2` using `type_weight_upper_unit (Fintype.card K) (Finset.Icc 1 N) (fun d => ((Finset.univ : Finset (Fin d → K)).filter (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card) n Fintype.one_lt_card (fun d hd => (Finset.mem_Icc.mp hd).1) (fun d hd => irreducible_count_upper_unit …`.

Establish `hZpos : (0 : ℝ) < ∏ d ∈ Finset.Icc 1 N, ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ))`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `d hd`. Establish `: (0 : ℝ) < d` using `by exact_mod_cast (Finset.mem_Icc.mp hd).1`. Check the signs of the components of the expression.

Establish `hfac : (0 : ℝ) < (N.factorial : ℝ)` using `by exact_mod_cast N.factorial_pos`. Establish `hc' : (S'.card : ℝ) * ∏ d ∈ Finset.Icc 1 N, ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ)) = (N.factorial : ℝ)` using `by exact_mod_cast hc`. Establish `step3 : 1 / ∏ d ∈ Finset.Icc 1 N, ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ)) = (S'.card : ℝ) / (N.factorial : ℝ)`. Rewrite using `[div_eq_div_iff hZpos.ne' hfac.ne', one_mul, hc']`. Establish `step4 : S'.card ≤ ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => σ.partition.parts = m)).card`.

Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `σ hσ`. Use `Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Apply `multiset_eq_of_count _ _ N (fun d hd => σ.partition.parts_pos hd) (by rw [σ.partition.parts_sum, Fintype.card_fin]) hm1 hm` to reduce the goal to its premises. Introduce `d hd`.

Rewrite using `[Equiv.Perm.parts_partition, Multiset.count_add, hS' σ hσ d hd, Multiset.count_replicate, if_neg (by have := (Finset.mem_Icc.mp hd).1; omega), add_zero]`. Combine the equalities or inequalities in the displayed calculation. Apply `div_le_div_of_nonneg_right _ hfac.le` to reduce the goal to its premises. Conclude with `step4` after adjusting the coercions.
-/
theorem type_weight_le (K : Type) [Field K] [Fintype K] (N : ℕ) (m : Multiset ℕ)
    (hm1 : ∀ d ∈ m, 1 ≤ d) (hm : m.sum = N) :
    ∑ c ∈ (sqSet K N).filter (fun c => degType (monicOf c) = m), sqWeight (monicOf c) ≤
      (((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun σ => σ.partition.parts = m)).card : ℝ) / (N.factorial : ℝ) := by
  classical
  set n : ℕ → ℕ := fun d => m.count d with hn
  have hsum : ∑ d ∈ Finset.Icc 1 N, d * n d = N := sum_mul_count_eq m N hm1 hm
  obtain ⟨S, hS, hSsum⟩ : ∃ S : Finset (Fin N → K),
      (∀ c ∈ sqSet K N, (∀ d ∈ Finset.Icc 1 N, (degType (monicOf c)).count d = n d) → c ∈ S) ∧
      ∑ c ∈ S, sqWeight (monicOf c) = _ :=
    ⟨_, fun c hc h => by simp only [Finset.mem_filter]; exact ⟨hc, h⟩,
      type_weight_exact K N n hsum⟩
  obtain ⟨S', hS', hc⟩ : ∃ S' : Finset (Equiv.Perm (Fin N)),
      (∀ σ ∈ S', ∀ d ∈ Finset.Icc 2 N, σ.cycleType.count d = n d) ∧
      S'.card * ∏ d ∈ Finset.Icc 1 N, (d ^ n d * (n d).factorial) = N.factorial :=
    ⟨_, fun σ hσ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ; exact hσ,
      cycle_type_probability N n hsum⟩
  have step1 : ∑ c ∈ (sqSet K N).filter (fun c => degType (monicOf c) = m),
      sqWeight (monicOf c) ≤ ∑ c ∈ S, sqWeight (monicOf c) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro c hc
      have hc' := Finset.mem_filter.mp hc
      exact hS c hc'.1 (fun d _ => by rw [hc'.2])
    · intro c _ _
      exact sqWeight_nonneg _
  have step2 := type_weight_upper_unit (Fintype.card K) (Finset.Icc 1 N)
    (fun d => ((Finset.univ : Finset (Fin d → K)).filter
      (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)).card) n
    Fintype.one_lt_card (fun d hd => (Finset.mem_Icc.mp hd).1)
    (fun d hd => irreducible_count_upper_unit K d (Finset.mem_Icc.mp hd).1)
  have hZpos : (0 : ℝ) < ∏ d ∈ Finset.Icc 1 N, ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ)) := by
    apply Finset.prod_pos
    intro d hd
    have : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    positivity
  have hfac : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  have hc' : (S'.card : ℝ) * ∏ d ∈ Finset.Icc 1 N, ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ)) =
      (N.factorial : ℝ) := by exact_mod_cast hc
  have step3 : 1 / ∏ d ∈ Finset.Icc 1 N, ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ)) =
      (S'.card : ℝ) / (N.factorial : ℝ) := by
    rw [div_eq_div_iff hZpos.ne' hfac.ne', one_mul, hc']
  have step4 : S'.card ≤ ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
        (fun σ => σ.partition.parts = m)).card := by
    apply Finset.card_le_card
    intro σ hσ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    apply multiset_eq_of_count _ _ N (fun d hd => σ.partition.parts_pos hd)
      (by rw [σ.partition.parts_sum, Fintype.card_fin]) hm1 hm
    intro d hd
    rw [Equiv.Perm.parts_partition, Multiset.count_add, hS' σ hσ d hd,
      Multiset.count_replicate, if_neg (by have := (Finset.mem_Icc.mp hd).1; omega), add_zero]
  calc _ ≤ ∑ c ∈ S, sqWeight (monicOf c) := step1
    _ = _ := hSsum
    _ ≤ _ := step2
    _ = (S'.card : ℝ) / (N.factorial : ℝ) := step3
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hfac.le
      exact_mod_cast step4

/- English proof (translation)
Introduce `K _ _ N A`. Use `set T : Finset (Multiset ℕ) := (Finset.univ : Finset N.Partition).image (fun p => p.parts) with hT`. Establish `hTmem : ∀ m : Multiset ℕ, (∀ d ∈ m, 1 ≤ d) → m.sum = N → m ∈ T`. Introduce `m h1 h2`. Conclude with `Finset.mem_image.mpr ⟨⟨m, fun {i} hi => h1 i hi, h2⟩, Finset.mem_univ _, rfl⟩`.

Establish `hTprop : ∀ m ∈ T, (∀ d ∈ m, 1 ≤ d) ∧ m.sum = N`. Introduce `m hm`. Take `⟨p, _, rfl⟩` from `Finset.mem_image.mp hm`. Conclude with `⟨fun d hd => p.parts_pos hd, p.parts_sum⟩`. Establish `hfac : (0 : ℝ) < (N.factorial : ℝ)` using `by exact_mod_cast N.factorial_pos`.

Rewrite using `[← Finset.sum_fiberwise_of_maps_to (t := T) (g := fun c => degType (monicOf c)) (fun c _ => hTmem _ (one_le_of_mem_degType _) (by rw [sum_degType _ (monicOf_monic c).ne_zero, monicOf_natDegree]))]`. Rewrite using `[Finset.card_eq_sum_card_fiberwise (t := T) (f := fun σ : Equiv.Perm (Fin N) => σ.partition.parts) (fun σ _ => hTmem _ (fun d hd => σ.partition.parts_pos hd) (by rw [σ.partition.parts_sum, Fintype.card_fin]))]`. Rewrite using `[Nat.cast_sum, Finset.sum_div]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `m hm`.

Take `⟨hm1, hm2⟩` from `hTprop m hm`. Distinguish the cases in `hA : A m`. Use `le_trans ?_ (le_trans (type_weight_le K N m hm1 hm2) ?_)` and prove the remaining obligations. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `c hc`.

Simplify using `only [Finset.mem_filter] at hc ⊢`. Conclude with `⟨hc.1.1, hc.2⟩`. Introduce `c _ _`. Conclude with `sqWeight_nonneg _`. Apply `div_le_div_of_nonneg_right _ hfac.le` to reduce the goal to its premises.

Apply `Nat.cast_le.mpr` to reduce the goal to its premises. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `σ hσ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢`. Conclude with `⟨hσ ▸ hA, hσ⟩`.

Rewrite using `[Finset.sum_eq_zero]`. Check the signs of the components of the expression. Introduce `c hc`. Simplify using `only [Finset.mem_filter] at hc`. Conclude with `absurd (hc.2 ▸ hc.1.2) hA`.
-/
theorem type_set_weight_bound : TypeSetWeight := by
  classical
  intro K _ _ N A
  set T : Finset (Multiset ℕ) := (Finset.univ : Finset N.Partition).image (fun p => p.parts)
    with hT
  have hTmem : ∀ m : Multiset ℕ, (∀ d ∈ m, 1 ≤ d) → m.sum = N → m ∈ T := by
    intro m h1 h2
    exact Finset.mem_image.mpr ⟨⟨m, fun {i} hi => h1 i hi, h2⟩, Finset.mem_univ _, rfl⟩
  have hTprop : ∀ m ∈ T, (∀ d ∈ m, 1 ≤ d) ∧ m.sum = N := by
    intro m hm
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨fun d hd => p.parts_pos hd, p.parts_sum⟩
  have hfac : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  rw [← Finset.sum_fiberwise_of_maps_to (t := T) (g := fun c => degType (monicOf c))
    (fun c _ => hTmem _ (one_le_of_mem_degType _)
      (by rw [sum_degType _ (monicOf_monic c).ne_zero, monicOf_natDegree]))]
  rw [Finset.card_eq_sum_card_fiberwise (t := T) (f := fun σ : Equiv.Perm (Fin N) => σ.partition.parts)
    (fun σ _ => hTmem _ (fun d hd => σ.partition.parts_pos hd)
      (by rw [σ.partition.parts_sum, Fintype.card_fin]))]
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro m hm
  obtain ⟨hm1, hm2⟩ := hTprop m hm
  by_cases hA : A m
  · refine le_trans ?_ (le_trans (type_weight_le K N m hm1 hm2) ?_)
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro c hc
        simp only [Finset.mem_filter] at hc ⊢
        exact ⟨hc.1.1, hc.2⟩
      · intro c _ _
        exact sqWeight_nonneg _
    · apply div_le_div_of_nonneg_right _ hfac.le
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      exact ⟨hσ ▸ hA, hσ⟩
  · rw [Finset.sum_eq_zero]
    · positivity
    · intro c hc
      simp only [Finset.mem_filter] at hc
      exact absurd (hc.2 ▸ hc.1.2) hA

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Unfold `sqWeight`. Rewrite using `[UniqueFactorizationMonoid.normalizedFactors_mul hf hg, Multiset.map_add, Multiset.prod_add]`.
-/
theorem sqWeight_mul {K : Type} [Field K] [Fintype K] (f g : K[X]) (hf : f ≠ 0) (hg : g ≠ 0) :
    sqWeight (f * g) = sqWeight f * sqWeight g := by
  classical
  unfold sqWeight
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hf hg, Multiset.map_add, Multiset.prod_add]

/- English proof (translation)
Use `set M := N - h.natDegree with hMdef`. Set `φ : (Fin N → K) → (Fin M → K)` to `fun c i => (monicOf c / h).coeff i`. Establish `hmul : ∀ c ∈ S, h * (monicOf c / h) = monicOf c` using `fun c hc => EuclideanDomain.mul_div_cancel' hmon.ne_zero (hS c hc).2`. Establish `hqmon : ∀ c ∈ S, (monicOf c / h).Monic` using `fun c hc => hmon.of_mul_monic_left (by rw [hmul c hc]; exact monicOf_monic c)`. Establish `hqdeg : ∀ c ∈ S, (monicOf c / h).natDegree = M`.

Introduce `c hc`. Establish `h1` using `hmon.natDegree_mul (hqmon c hc)`. Rewrite `h1` using `[hmul c hc, monicOf_natDegree]`. Use linear arithmetic over natural numbers and integers. Establish `hφ : ∀ c ∈ S, monicOf (φ c) = monicOf c / h` using `fun c hc => monicOf_coeffs (hqmon c hc) (hqdeg c hc)`.

Establish `hφmem : ∀ c ∈ S, φ c ∈ sqSet K M`. Introduce `c hc`. Establish `hc'` using `(mem_sqSet c).mp (hS c hc).1`. Rewrite using `[mem_sqSet, hφ c hc]`. Use `⟨hc'.1.squarefree_of_dvd ⟨h, by rw [mul_comm, hmul c hc]⟩, ?_⟩` and prove the remaining obligations.

Introduce `h0`. Apply `hc'.2` to reduce the goal to its premises. Rewrite using `[← hmul c hc, Polynomial.mul_coeff_zero, h0, mul_zero]`. Establish `hinj : Set.InjOn φ (S : Set (Fin N → K))`. Introduce `c1 h1 c2 h2 he`.

Apply `monicOf_injective` to reduce the goal to its premises. Rewrite using `[← hmul c1 h1, ← hmul c2 h2, ← hφ c1 h1, ← hφ c2 h2, he]`. Establish `hw : ∀ c ∈ S, sqWeight (monicOf c) = sqWeight h * sqWeight (monicOf (φ c))`. Introduce `c hc`. Rewrite using `[hφ c hc, ← sqWeight_mul _ _ hmon.ne_zero (hqmon c hc).ne_zero, hmul c hc]`.

Rewrite using `[Finset.sum_congr rfl hw, ← Finset.mul_sum]`. Establish `h1 : ∑ c ∈ S, sqWeight (monicOf (φ c)) ≤ 1`. Rewrite using `[← Finset.sum_image (f := fun c' => sqWeight (monicOf c')) hinj]`. Use `le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hM K M)` and prove the remaining obligations. Introduce `c' hc'`.

Take `⟨c, hc, rfl⟩` from `Finset.mem_image.mp hc'`. Conclude with `hφmem c hc`. Introduce `c' _ _`. Conclude with `sqWeight_nonneg _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem divisor_square_weight_sum_le (hM : SqMassLeOne) (K : Type) [Field K] [Fintype K] (N : ℕ) (h : K[X])
    (hmon : h.Monic) (hdeg : h.natDegree ≤ N) (S : Finset (Fin N → K))
    (hS : ∀ c ∈ S, c ∈ sqSet K N ∧ h ∣ monicOf c) :
    ∑ c ∈ S, sqWeight (monicOf c) ≤ sqWeight h := by
  classical
  set M := N - h.natDegree with hMdef
  let φ : (Fin N → K) → (Fin M → K) := fun c i => (monicOf c / h).coeff i
  have hmul : ∀ c ∈ S, h * (monicOf c / h) = monicOf c := fun c hc =>
    EuclideanDomain.mul_div_cancel' hmon.ne_zero (hS c hc).2
  have hqmon : ∀ c ∈ S, (monicOf c / h).Monic := fun c hc =>
    hmon.of_mul_monic_left (by rw [hmul c hc]; exact monicOf_monic c)
  have hqdeg : ∀ c ∈ S, (monicOf c / h).natDegree = M := by
    intro c hc
    have h1 := hmon.natDegree_mul (hqmon c hc)
    rw [hmul c hc, monicOf_natDegree] at h1
    omega
  have hφ : ∀ c ∈ S, monicOf (φ c) = monicOf c / h := fun c hc =>
    monicOf_coeffs (hqmon c hc) (hqdeg c hc)
  have hφmem : ∀ c ∈ S, φ c ∈ sqSet K M := by
    intro c hc
    have hc' := (mem_sqSet c).mp (hS c hc).1
    rw [mem_sqSet, hφ c hc]
    refine ⟨hc'.1.squarefree_of_dvd ⟨h, by rw [mul_comm, hmul c hc]⟩, ?_⟩
    intro h0
    apply hc'.2
    rw [← hmul c hc, Polynomial.mul_coeff_zero, h0, mul_zero]
  have hinj : Set.InjOn φ (S : Set (Fin N → K)) := by
    intro c1 h1 c2 h2 he
    apply monicOf_injective
    rw [← hmul c1 h1, ← hmul c2 h2, ← hφ c1 h1, ← hφ c2 h2, he]
  have hw : ∀ c ∈ S, sqWeight (monicOf c) = sqWeight h * sqWeight (monicOf (φ c)) := by
    intro c hc
    rw [hφ c hc, ← sqWeight_mul _ _ hmon.ne_zero (hqmon c hc).ne_zero, hmul c hc]
  rw [Finset.sum_congr rfl hw, ← Finset.mul_sum]
  have h1 : ∑ c ∈ S, sqWeight (monicOf (φ c)) ≤ 1 := by
    rw [← Finset.sum_image (f := fun c' => sqWeight (monicOf c')) hinj]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hM K M)
    · intro c' hc'
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hc'
      exact hφmem c hc
    · intro c' _ _
      exact sqWeight_nonneg _
  calc sqWeight h * ∑ c ∈ S, sqWeight (monicOf (φ c)) ≤ sqWeight h * 1 :=
        mul_le_mul_of_nonneg_left h1 (sqWeight_nonneg h)
    _ = sqWeight h := mul_one _

/- English proof (translation)
Introduce `K _ _ N h hmon _ _ hdeg`. Conclude with `divisor_square_weight_sum_le hM K N h hmon hdeg _ (fun c hc => (Finset.mem_filter.1 hc))`.
-/
theorem divisorBound_of (hM : SqMassLeOne) : DivisorBound := by
  classical
  intro K _ _ N h hmon _ _ hdeg
  exact divisor_square_weight_sum_le hM K N h hmon hdeg _ (fun c hc => (Finset.mem_filter.1 hc))

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `n K _ _ _ _ Φ EE hlt htrans hEE hnot`. Establish `hm : ∀ u : Matrix n n K, u ∈ rootSet' Φ ↔ (∀ a, u a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ Φ → u a b = 0` using `fun u => Iff.rfl`. Establish `hterm : ∀ u ∈ rootSet' (K` using `K) Φ, ∀ u' ∈ rootSet' (K := K) Φ, ∀ a b c, ¬ ((a, c) ∈ Φ ∧ (c, b) ∈ Φ) → c ≠ a → c ≠ b → u a c * u' c b = 0 := by`. Introduce `u hu u' hu' a b c h hca hcb`. Rewrite `hu`, `hu'` using `[hm]`.

Distinguish the cases in `h1 : (a, c) ∈ Φ`. Rewrite using `[hu'.2 c b hcb (fun h2 => h ⟨h1, h2⟩), mul_zero]`. Rewrite using `[hu.2 a c (Ne.symm hca) h1, zero_mul]`. Establish `hmul : ∀ u ∈ rootSet' (K` using `K) Φ, ∀ u' ∈ rootSet' (K := K) Φ, u * u' ∈ rootSet' Φ ∧ ∀ x ∈ EE, (u * u') x.1 x.2 = u x.1 x.2 + u' x.1 x.2 := by`. Introduce `u hu u' hu'`.

Establish `hu1` using `(hm u).1 hu`. Establish `hu1'` using `(hm u').1 hu'`. Use `⟨(hm _).2 ⟨fun a => ?_, fun a b hab hΦ => ?_⟩, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Rewrite using `[hu1.1, hu1'.1, mul_one]`.

Introduce `c _ hca`. Use `hterm u hu u' hu' a a c (fun h => ?_) hca hca` and prove the remaining obligations. Conclude with `absurd (lt_trans (hlt _ h.1) (hlt _ h.2)) (lt_irrefl a)`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.mul_apply]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `c _`. Distinguish the cases in `hca : c = a`. Substitute `hca` using the available equality. Rewrite using `[hu1'.2 c b hab hΦ, mul_zero]`.

Distinguish the cases in `hcb : c = b`. Substitute `hcb` using the available equality. Rewrite using `[hu1.2 a c hab hΦ, zero_mul]`. Conclude with `hterm u hu u' hu' a b c (fun h => hΦ (htrans a c b h.1 h.2)) hca hcb`. Establish `hxΦ` using `hEE hx`.

Establish `hne : x.1 ≠ x.2` using `(hlt x hxΦ).ne`. Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_add x.1 x.2 hne]`. Rewrite using `[hu1.1, hu1'.1, one_mul, mul_one, add_comm]`. Introduce and unpack `c ⟨hca, hcb⟩`. Use `hterm u hu u' hu' x.1 x.2 c (fun h => ?_) hca hcb` and prove the remaining obligations.

Conclude with `hnot x.1 c x.2 h.1 h.2 (by simpa using hx)`. Establish `hone : (1 : Matrix n n K) ∈ rootSet' Φ` using `(hm _).2 ⟨fun a => Matrix.one_apply_eq a, fun a b hab _ => Matrix.one_apply_ne hab⟩`. Establish `hpow : ∀ u ∈ rootSet' (K` using `K) Φ, ∀ k : ℕ, u ^ k ∈ rootSet' (K := K) Φ := by`. Introduce `u hu k`. Proceed by induction on `k with`.

Consider the case `zero => rw [pow_zero]`. Conclude with `hone`. Consider the case `succ k ih => rw [pow_succ]`. Conclude with `(hmul _ ih _ hu).1`. Use `⟨hone, hmul, fun u hu => ?_, ?_⟩` and prove the remaining obligations.

Establish `hu1` using `(hm u).1 hu`. Establish `htri : u.BlockTriangular id`. Introduce `i j hji`. Conclude with `hu1.2 i j (ne_of_gt hji) (fun h => absurd (hlt _ h) (not_lt.2 (le_of_lt hji)))`. Establish `hdet : u.det = 1`.

Rewrite using `[Matrix.det_of_upperTriangular htri]`. Simplify using `[hu1.1]`. Establish `hunit : IsUnit u` using `(Matrix.isUnit_iff_isUnit_det u).2 (by rw [hdet]; exact isUnit_one)`. Take `⟨k, hk, hku⟩` from `isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite hunit.unit)`. Establish `hku' : u ^ k = 1`.

Use `congrArg (fun w : (Matrix n n K)ˣ => (w : Matrix n n K)) hku` as an intermediate fact. Simplify using `using this`. Use `⟨u ^ (k - 1), hpow u hu _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← pow_succ', Nat.sub_add_cancel hk, hku']`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hk, hku']`.

Set `e : (rootSet' (K` to `K) Φ) ≃ (Φ → K) := { toFun := fun u p => (u : Matrix n n K) p.1.1 p.1.2 invFun := fun f => ⟨Matrix.of fun a b => if a = b then 1 else if h : (a, b) ∈ Φ then f ⟨(a, b), h⟩ else 0, (hm _).2 ⟨fun a => by simp, fun a b hab hΦ => by simp [hab, hΦ]⟩⟩ left_inv := fun u => by`. Establish `hu1` using `(hm _).1 u.2`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `a b`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using `[hu1.1]`. Distinguish the cases in `hΦ : (a, b) ∈ Φ`. Simplify using `[hab, hΦ]`. Simplify using `[hab, hΦ, hu1.2 a b hab hΦ]`.

Use `right_inv := fun f => by`. Use function extensionality and compare the values at `p`. Establish `hne : p.1.1 ≠ p.1.2` using `(hlt p.1 p.2).ne`. Simplify using `[hne] }`. Rewrite using `[Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_coe]`.
-/
theorem root_set_group : RootSetGroup := by
  intro n K _ _ _ _ Φ EE hlt htrans hEE hnot
  classical
  have hm : ∀ u : Matrix n n K, u ∈ rootSet' Φ ↔
      (∀ a, u a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ Φ → u a b = 0 := fun u => Iff.rfl
  have hterm : ∀ u ∈ rootSet' (K := K) Φ, ∀ u' ∈ rootSet' (K := K) Φ, ∀ a b c,
      ¬ ((a, c) ∈ Φ ∧ (c, b) ∈ Φ) → c ≠ a → c ≠ b → u a c * u' c b = 0 := by
    intro u hu u' hu' a b c h hca hcb
    rw [hm] at hu hu'
    by_cases h1 : (a, c) ∈ Φ
    · rw [hu'.2 c b hcb (fun h2 => h ⟨h1, h2⟩), mul_zero]
    · rw [hu.2 a c (Ne.symm hca) h1, zero_mul]
  have hmul : ∀ u ∈ rootSet' (K := K) Φ, ∀ u' ∈ rootSet' (K := K) Φ, u * u' ∈ rootSet' Φ ∧
      ∀ x ∈ EE, (u * u') x.1 x.2 = u x.1 x.2 + u' x.1 x.2 := by
    intro u hu u' hu'
    have hu1 := (hm u).1 hu
    have hu1' := (hm u').1 hu'
    refine ⟨(hm _).2 ⟨fun a => ?_, fun a b hab hΦ => ?_⟩, fun x hx => ?_⟩
    · rw [Matrix.mul_apply, Finset.sum_eq_single a]
      · rw [hu1.1, hu1'.1, mul_one]
      · intro c _ hca
        refine hterm u hu u' hu' a a c (fun h => ?_) hca hca
        exact absurd (lt_trans (hlt _ h.1) (hlt _ h.2)) (lt_irrefl a)
      · simp
    · rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro c _
      by_cases hca : c = a
      · subst hca
        rw [hu1'.2 c b hab hΦ, mul_zero]
      by_cases hcb : c = b
      · subst hcb
        rw [hu1.2 a c hab hΦ, zero_mul]
      exact hterm u hu u' hu' a b c (fun h => hΦ (htrans a c b h.1 h.2)) hca hcb
    · have hxΦ := hEE hx
      have hne : x.1 ≠ x.2 := (hlt x hxΦ).ne
      rw [Matrix.mul_apply, Fintype.sum_eq_add x.1 x.2 hne]
      · rw [hu1.1, hu1'.1, one_mul, mul_one, add_comm]
      · rintro c ⟨hca, hcb⟩
        refine hterm u hu u' hu' x.1 x.2 c (fun h => ?_) hca hcb
        exact hnot x.1 c x.2 h.1 h.2 (by simpa using hx)
  have hone : (1 : Matrix n n K) ∈ rootSet' Φ :=
    (hm _).2 ⟨fun a => Matrix.one_apply_eq a, fun a b hab _ => Matrix.one_apply_ne hab⟩
  have hpow : ∀ u ∈ rootSet' (K := K) Φ, ∀ k : ℕ, u ^ k ∈ rootSet' (K := K) Φ := by
    intro u hu k
    induction k with
    | zero => rw [pow_zero]; exact hone
    | succ k ih => rw [pow_succ]; exact (hmul _ ih _ hu).1
  refine ⟨hone, hmul, fun u hu => ?_, ?_⟩
  · have hu1 := (hm u).1 hu
    have htri : u.BlockTriangular id := by
      intro i j hji
      exact hu1.2 i j (ne_of_gt hji) (fun h => absurd (hlt _ h) (not_lt.2 (le_of_lt hji)))
    have hdet : u.det = 1 := by
      rw [Matrix.det_of_upperTriangular htri]
      simp [hu1.1]
    have hunit : IsUnit u := (Matrix.isUnit_iff_isUnit_det u).2 (by rw [hdet]; exact isUnit_one)
    obtain ⟨k, hk, hku⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite hunit.unit)
    have hku' : u ^ k = 1 := by
      have := congrArg (fun w : (Matrix n n K)ˣ => (w : Matrix n n K)) hku
      simpa using this
    refine ⟨u ^ (k - 1), hpow u hu _, ?_, ?_⟩
    · rw [← pow_succ', Nat.sub_add_cancel hk, hku']
    · rw [← pow_succ, Nat.sub_add_cancel hk, hku']
  · let e : (rootSet' (K := K) Φ) ≃ (Φ → K) :=
      { toFun := fun u p => (u : Matrix n n K) p.1.1 p.1.2
        invFun := fun f => ⟨Matrix.of fun a b => if a = b then 1 else
            if h : (a, b) ∈ Φ then f ⟨(a, b), h⟩ else 0,
          (hm _).2 ⟨fun a => by simp, fun a b hab hΦ => by simp [hab, hΦ]⟩⟩
        left_inv := fun u => by
          have hu1 := (hm _).1 u.2
          apply Subtype.ext
          ext a b
          by_cases hab : a = b
          · subst hab
            simp [hu1.1]
          · by_cases hΦ : (a, b) ∈ Φ
            · simp [hab, hΦ]
            · simp [hab, hΦ, hu1.2 a b hab hΦ]
        right_inv := fun f => by
          funext p
          have hne : p.1.1 ≠ p.1.2 := (hlt p.1 p.2).ne
          simp [hne] }
    rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_coe]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Rewrite using `[Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product_right]`. Establish `hj : ∀ j : Fin N, (∑ i : Fin N, if (i, j).1 < (i, j).2 then 1 else 0) = (j : ℕ)`. Introduce `j`. Use `show (∑ i : Fin N, if i < j then 1 else 0) = (j : ℕ)`. Rewrite using `[← Finset.card_filter]`.

Establish `e : Finset.univ.filter (fun i : Fin N => i < j) = Finset.Iio j`. Use extensionality with `i`. Simplify using the standard rewrite rules. Rewrite using `[e, Fin.card_Iio]`. Rewrite using `[Finset.sum_congr rfl (fun j _ => hj j), Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]`.
-/
theorem card_lt_pairs (N : ℕ) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun x => x.1 < x.2)).card = N * (N - 1) / 2 := by
  rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product_right]
  have hj : ∀ j : Fin N, (∑ i : Fin N, if (i, j).1 < (i, j).2 then 1 else 0) = (j : ℕ) := by
    intro j
    show (∑ i : Fin N, if i < j then 1 else 0) = (j : ℕ)
    rw [← Finset.card_filter]
    have e : Finset.univ.filter (fun i : Fin N => i < j) = Finset.Iio j := by
      ext i
      simp
    rw [e, Fin.card_Iio]
  rw [Finset.sum_congr rfl (fun j _ => hj j), Fin.sum_univ_eq_sum_range (fun i => i) N,
    Finset.sum_range_id]

/- English proof (translation)
Introduce `K _ _ s k N hskN`. Use `set P : Finset (Fin N × Fin N) := Finset.univ.filter (fun x : Fin N × Fin N => x.1 < x.2 ∧ ¬ ((s ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) < s + k) ∧ (x.2 : ℕ) = s + k)) with hP`. Set `good : Matrix (Fin N) (Fin N) K → Prop` to `fun u => (∀ i, u i i = 1) ∧ (∀ i j, j < i → u i j = 0) ∧ ∀ i j : Fin N, s ≤ (i : ℕ) → (i : ℕ) < s + k → (j : ℕ) = s + k → u i j = 0`. Establish `hdet : ∀ u, good u → u.det = 1`. Introduce `u hu`.

Rewrite using `[Matrix.det_of_upperTriangular (fun i j hji => hu.2.1 i j hji)]`. Simplify using `[hu.1]`. Establish `hzero : ∀ u, good u → ∀ i j, i ≠ j → (i, j) ∉ P → u i j = 0`. Introduce `u hu i j hij hP'`. Break down `lt_or_gt_of_ne hij with h | h` into its components or cases.

Distinguish the cases in `hB : (s ≤ (i : ℕ) ∧ (i : ℕ) < s + k) ∧ (j : ℕ) = s + k`. Conclude with `hu.2.2 i j hB.1.1 hB.1.2 hB.2`. Conclude with `absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, h, hB⟩) hP'`. Conclude with `hu.2.1 i j h`. Set `M : (P → K) → Matrix (Fin N) (Fin N) K` to `fun f => Matrix.of fun a b => if a = b then 1 else if h : (a, b) ∈ P then f ⟨(a, b), h⟩ else 0`.

Establish `hMgood : ∀ f, good (M f)`. Introduce `f`. Use `⟨fun a => by simp [M], fun i j hji => ?_, fun i j hi1 hi2 hj => ?_⟩` and prove the remaining obligations. Establish `hne : i ≠ j` using `(ne_of_gt hji)`. Establish `hnP : (i, j) ∉ P` using `fun h => absurd (Finset.mem_filter.1 h).2.1 (not_lt.2 hji.le)`.

Simplify using `[M, hne, hnP]`. Establish `hne : i ≠ j`. Introduce `h`. Rewrite `hi2` using `[h]`. Use linear arithmetic over natural numbers and integers.

Establish `hnP : (i, j) ∉ P` using `fun h => (Finset.mem_filter.1 h).2.2 ⟨⟨hi1, hi2⟩, hj⟩`. Simplify using `[M, hne, hnP]`. Establish `hU : ∀ f, IsUnit (M f).det` using `fun f => by rw [hdet _ (hMgood f)]; exact isUnit_one`. Establish `hmem : ∀ u : GL (Fin N) K, u ∈ besselSet K s k N ↔ good (u : Matrix (Fin N) (Fin N) K)` using `fun u => Iff.rfl`. Set `e : (besselSet K s k N) ≃ (P → K)` to `{ toFun := fun u p => ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) p.1.1 p.1.2 invFun := fun f => ⟨Matrix.nonsingInvUnit (M f) (hU f), by`.

Rewrite using `[hmem]`. Conclude with `hMgood f⟩`. Use `left_inv := fun u => by`. Establish `hu1 : good ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)` using `(hmem _).1 u.2`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Use `show M (fun p => ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) p.1.1 p.1.2) = ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)`. Use extensionality with `a b`. Simplify using `only [M, Matrix.of_apply]`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using `[hu1.1]`. Distinguish the cases in `hΦ : (a, b) ∈ P`. Simplify using `[hab, hΦ]`. Simplify using `[hab, hΦ, hzero _ hu1 a b hab hΦ]`.

Use `right_inv := fun f => by`. Use function extensionality and compare the values at `p`. Establish `hne : p.1.1 ≠ p.1.2` using `(Finset.mem_filter.1 p.2).2.1.ne`. Use `show M f p.1.1 p.1.2 = f p`. Simplify using `[M, hne] }`.

Rewrite using `[Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_coe]`. Use `congr 1`. Use `set L := (Finset.univ : Finset (Fin N × Fin N)).filter (fun x => x.1 < x.2) with hL`. Establish `hPL : P = L.filter (fun x => ¬ ((s ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) < s + k) ∧ (x.2 : ℕ) = s + k))`. Rewrite using `[hP, hL, Finset.filter_filter]`.

Establish `hadd` using `Finset.card_filter_add_card_filter_not (s := L) (fun x : Fin N × Fin N => (s ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) < s + k) ∧ (x.2 : ℕ) = s + k)`. Use `beta_reduce at hadd`. Establish `hZ : (L.filter (fun x : Fin N × Fin N => (s ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) < s + k) ∧ (x.2 : ℕ) = s + k)).card = k`. Establish `hsk : s + k < N` using `by omega`. Set `g : ℕ → Fin N × Fin N` to `fun i => (⟨min i (N - 1), by omega⟩, ⟨s + k, hsk⟩)`.

Establish `himg : L.filter (fun x : Fin N × Fin N => (s ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) < s + k) ∧ (x.2 : ℕ) = s + k) = (Finset.Ico s (s + k)).image g`. Use extensionality with `⟨i, j⟩`. Simplify using `only [hL, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_Ico, g, Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, ⟨h1, h2⟩, h3⟩`.

Use `⟨(i : ℕ), ⟨h1, h2⟩, Fin.ext ?_, Fin.ext h3.symm⟩` and prove the remaining obligations. Use `show min (i : ℕ) (N - 1) = i`. Use `i.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨a, ⟨h1, h2⟩, rfl, rfl⟩`.

Use `⟨?_, ⟨?_, ?_⟩, rfl⟩` and prove the remaining obligations. Use `show min a (N - 1) < s + k`. Use linear arithmetic over natural numbers and integers. Use `show s ≤ min a (N - 1)`. Use linear arithmetic over natural numbers and integers.

Use `show min a (N - 1) < s + k`. Use linear arithmetic over natural numbers and integers. Rewrite using `[himg, Finset.card_image_of_injOn, Nat.card_Ico]`. Use linear arithmetic over natural numbers and integers. Introduce `a ha b hb hab`.

Simplify using `only [Finset.coe_Ico, Set.mem_Ico] at ha hb`. Use `congrArg (fun x : Fin N × Fin N => (x.1 : ℕ)) hab` as an intermediate fact. Simplify using `only [g] at this`. Use linear arithmetic over natural numbers and integers. Establish `hLc : L.card = N * (N - 1) / 2` using `by rw [hL]; exact card_lt_pairs N`.

Rewrite using `[hPL]`. Generalize the expression as in `N * (N - 1) / 2 = T at hLc ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem bessel_set_cardinality : BesselCard := by
  intro K _ _ s k N hskN
  classical
  set P : Finset (Fin N × Fin N) := Finset.univ.filter (fun x : Fin N × Fin N => x.1 < x.2 ∧
    ¬ ((s ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) < s + k) ∧ (x.2 : ℕ) = s + k)) with hP
  let good : Matrix (Fin N) (Fin N) K → Prop := fun u => (∀ i, u i i = 1) ∧
    (∀ i j, j < i → u i j = 0) ∧
    ∀ i j : Fin N, s ≤ (i : ℕ) → (i : ℕ) < s + k → (j : ℕ) = s + k → u i j = 0
  have hdet : ∀ u, good u → u.det = 1 := by
    intro u hu
    rw [Matrix.det_of_upperTriangular (fun i j hji => hu.2.1 i j hji)]
    simp [hu.1]
  have hzero : ∀ u, good u → ∀ i j, i ≠ j → (i, j) ∉ P → u i j = 0 := by
    intro u hu i j hij hP'
    rcases lt_or_gt_of_ne hij with h | h
    · by_cases hB : (s ≤ (i : ℕ) ∧ (i : ℕ) < s + k) ∧ (j : ℕ) = s + k
      · exact hu.2.2 i j hB.1.1 hB.1.2 hB.2
      · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, h, hB⟩) hP'
    · exact hu.2.1 i j h
  let M : (P → K) → Matrix (Fin N) (Fin N) K := fun f => Matrix.of fun a b =>
    if a = b then 1 else if h : (a, b) ∈ P then f ⟨(a, b), h⟩ else 0
  have hMgood : ∀ f, good (M f) := by
    intro f
    refine ⟨fun a => by simp [M], fun i j hji => ?_, fun i j hi1 hi2 hj => ?_⟩
    · have hne : i ≠ j := (ne_of_gt hji)
      have hnP : (i, j) ∉ P := fun h => absurd (Finset.mem_filter.1 h).2.1 (not_lt.2 hji.le)
      simp [M, hne, hnP]
    · have hne : i ≠ j := by
        intro h
        rw [h] at hi2
        omega
      have hnP : (i, j) ∉ P := fun h => (Finset.mem_filter.1 h).2.2 ⟨⟨hi1, hi2⟩, hj⟩
      simp [M, hne, hnP]
  have hU : ∀ f, IsUnit (M f).det := fun f => by rw [hdet _ (hMgood f)]; exact isUnit_one
  have hmem : ∀ u : GL (Fin N) K, u ∈ besselSet K s k N ↔ good (u : Matrix (Fin N) (Fin N) K) :=
    fun u => Iff.rfl
  let e : (besselSet K s k N) ≃ (P → K) :=
    { toFun := fun u p => ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.nonsingInvUnit (M f) (hU f), by
        rw [hmem]
        exact hMgood f⟩
      left_inv := fun u => by
        have hu1 : good ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := (hmem _).1 u.2
        apply Subtype.ext
        apply Units.ext
        show M (fun p => ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) p.1.1 p.1.2) =
          ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)
        ext a b
        simp only [M, Matrix.of_apply]
        by_cases hab : a = b
        · subst hab
          simp [hu1.1]
        · by_cases hΦ : (a, b) ∈ P
          · simp [hab, hΦ]
          · simp [hab, hΦ, hzero _ hu1 a b hab hΦ]
      right_inv := fun f => by
        funext p
        have hne : p.1.1 ≠ p.1.2 := (Finset.mem_filter.1 p.2).2.1.ne
        show M f p.1.1 p.1.2 = f p
        simp [M, hne] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_coe]
  congr 1
  set L := (Finset.univ : Finset (Fin N × Fin N)).filter (fun x => x.1 < x.2) with hL
  have hPL : P = L.filter (fun x => ¬ ((s ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) < s + k) ∧ (x.2 : ℕ) = s + k)) := by
    rw [hP, hL, Finset.filter_filter]
  have hadd := Finset.card_filter_add_card_filter_not (s := L)
    (fun x : Fin N × Fin N => (s ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) < s + k) ∧ (x.2 : ℕ) = s + k)
  beta_reduce at hadd
  have hZ : (L.filter (fun x : Fin N × Fin N =>
      (s ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) < s + k) ∧ (x.2 : ℕ) = s + k)).card = k := by
    have hsk : s + k < N := by omega
    let g : ℕ → Fin N × Fin N := fun i => (⟨min i (N - 1), by omega⟩, ⟨s + k, hsk⟩)
    have himg : L.filter (fun x : Fin N × Fin N =>
        (s ≤ (x.1 : ℕ) ∧ (x.1 : ℕ) < s + k) ∧ (x.2 : ℕ) = s + k) = (Finset.Ico s (s + k)).image g := by
      ext ⟨i, j⟩
      simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_Ico, g, Prod.mk.injEq]
      constructor
      · rintro ⟨-, ⟨h1, h2⟩, h3⟩
        refine ⟨(i : ℕ), ⟨h1, h2⟩, Fin.ext ?_, Fin.ext h3.symm⟩
        show min (i : ℕ) (N - 1) = i
        have := i.2
        omega
      · rintro ⟨a, ⟨h1, h2⟩, rfl, rfl⟩
        refine ⟨?_, ⟨?_, ?_⟩, rfl⟩
        · show min a (N - 1) < s + k
          omega
        · show s ≤ min a (N - 1)
          omega
        · show min a (N - 1) < s + k
          omega
    rw [himg, Finset.card_image_of_injOn, Nat.card_Ico]
    · omega
    · intro a ha b hb hab
      simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
      have := congrArg (fun x : Fin N × Fin N => (x.1 : ℕ)) hab
      simp only [g] at this
      omega
  have hLc : L.card = N * (N - 1) / 2 := by rw [hL]; exact card_lt_pairs N
  rw [hPL]
  generalize N * (N - 1) / 2 = T at hLc ⊢
  omega

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Polynomial

noncomputable def wtOf {α : Type} [Fintype α] (μ : α → ℝ) (S : Set α) : ℝ := ∑ x, S.indicator μ x

section aux
variable {α β : Type} [Fintype α]

/- English proof (translation)
Unfold `wtOf`. Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl (fun x _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases h : p x <;> simp [Set.indicator, h]`.
-/
theorem wtOf_eq_filter (μ : α → ℝ) (p : α → Prop) [DecidablePred p] :
    wtOf μ {x | p x} = ∑ x ∈ Finset.univ.filter p, μ x := by
  unfold wtOf
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : p x <;> simp [Set.indicator, h]

/- English proof (translation)
Unfold `wtOf`. Rewrite using `[Finset.sum_filter, ← Finset.sum_subset (Finset.subset_univ s)]`. Use `Finset.sum_congr rfl (fun x hx => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases h : p x <;> simp [Set.indicator, h, hx]`. Introduce `x _ hx`.

Simplify using `[Set.indicator, hx]`.
-/
theorem wtOf_eq_filter' (μ : α → ℝ) (s : Finset α) (p : α → Prop) [DecidablePred p] :
    wtOf μ {x | x ∈ s ∧ p x} = ∑ x ∈ s.filter p, μ x := by
  unfold wtOf
  rw [Finset.sum_filter, ← Finset.sum_subset (Finset.subset_univ s)]
  · refine Finset.sum_congr rfl (fun x hx => ?_)
    by_cases h : p x <;> simp [Set.indicator, h, hx]
  · intro x _ hx
    simp [Set.indicator, hx]

/- English proof (translation)
Unfold `wtOf`. Conclude with `Finset.sum_le_sum (fun x _ => Set.indicator_le_indicator_of_subset h hμ x)`.
-/
theorem wtOf_mono (μ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x) {S T : Set α} (h : S ⊆ T) :
    wtOf μ S ≤ wtOf μ T := by
  unfold wtOf
  exact Finset.sum_le_sum (fun x _ => Set.indicator_le_indicator_of_subset h hμ x)

/- English proof (translation)
Unfold `wtOf`. Conclude with `Finset.sum_nonneg (fun x _ => Set.indicator_nonneg (fun y _ => hμ y) x)`.
-/
theorem wtOf_nonneg (μ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x) (S : Set α) : 0 ≤ wtOf μ S := by
  unfold wtOf
  exact Finset.sum_nonneg (fun x _ => Set.indicator_nonneg (fun y _ => hμ y) x)

/- English proof (translation)
Unfold `wtOf`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum (fun x _ => ?_)` and prove the remaining obligations. Use `hμ x` as an intermediate fact. Apply the tactic sequence `by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> simp [Set.indicator, hS, hT] <;> linarith`.
-/
theorem wtOf_union_le (μ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x) (S T : Set α) :
    wtOf μ (S ∪ T) ≤ wtOf μ S + wtOf μ T := by
  unfold wtOf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun x _ => ?_)
  have := hμ x
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> simp [Set.indicator, hS, hT] <;> linarith

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simp [wtOf]`. Consider the case `insert b t hb ih`. Rewrite using `[Finset.set_biUnion_insert, Finset.sum_insert hb]`. Conclude with `(wtOf_union_le μ hμ _ _).trans (by linarith)`.
-/
theorem wtOf_biUnion_le (μ : α → ℝ) (hμ : ∀ x, 0 ≤ μ x) (t : Finset β) (S : β → Set α) :
    wtOf μ (⋃ b ∈ t, S b) ≤ ∑ b ∈ t, wtOf μ (S b) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [wtOf]
  | insert b t hb ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hb]
    exact (wtOf_union_le μ hμ _ _).trans (by linarith)

/- English proof (translation)
Simplify using `only [wtOf, Set.indicator_compl, Set.indicator_univ, Pi.sub_apply, Finset.sum_sub_distrib]`.
-/
theorem wtOf_compl (μ : α → ℝ) (S : Set α) : wtOf μ Sᶜ = wtOf μ Set.univ - wtOf μ S := by
  simp only [wtOf, Set.indicator_compl, Set.indicator_univ, Pi.sub_apply, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `[wtOf]`.
-/
theorem wtOf_univ (μ : α → ℝ) : wtOf μ Set.univ = ∑ x, μ x := by
  simp [wtOf]

end aux

section prod
variable {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]

/- English proof (translation)
Unfold `wtOf`. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`. Use `Finset.sum_congr rfl (fun x _ => ?_)` and prove the remaining obligations. Distinguish the cases in `h : ∀ v, x v ∈ S v`. Rewrite using `[Set.indicator_of_mem (show x ∈ {x : ι → Ω | ∀ v, x v ∈ S v} from h)]`.

Conclude with `Finset.prod_congr rfl (fun v _ => (Set.indicator_of_mem (h v) P).symm)`. Use `push_neg at h`. Take `⟨v, hv⟩` from `h`. Establish `h0 : x ∉ {x : ι → Ω | ∀ v, x v ∈ S v}` using `fun hx => hv (hx v)`. Establish `h1 : Set.indicator (S v) P (x v) = 0` using `by simp [Set.indicator, hv]`.

Rewrite using `[Set.indicator_apply, if_neg h0, Finset.prod_eq_zero (Finset.mem_univ v) h1]`.
-/
theorem wtOf_pi (P : Ω → ℝ) (S : ι → Set Ω) :
    wtOf (fun x : ι → Ω => ∏ v, P (x v)) {x | ∀ v, x v ∈ S v} = ∏ v, wtOf P (S v) := by
  classical
  unfold wtOf
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : ∀ v, x v ∈ S v
  · rw [Set.indicator_of_mem (show x ∈ {x : ι → Ω | ∀ v, x v ∈ S v} from h)]
    exact Finset.prod_congr rfl (fun v _ => (Set.indicator_of_mem (h v) P).symm)
  · push_neg at h
    obtain ⟨v, hv⟩ := h
    have h0 : x ∉ {x : ι → Ω | ∀ v, x v ∈ S v} := fun hx => hv (hx v)
    have h1 : Set.indicator (S v) P (x v) = 0 := by simp [Set.indicator, hv]
    rw [Set.indicator_apply, if_neg h0, Finset.prod_eq_zero (Finset.mem_univ v) h1]

/- English proof (translation)
Establish `hset : {x : ι → Ω | x v₀ ∈ S} = {x : ι → Ω | ∀ v, x v ∈ (if v = v₀ then S else Set.univ)}`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h v split_ifs with hv`.

Substitute `hv` using the available equality. Conclude with `h`. Conclude with `Set.mem_univ _`. Introduce `h`. Simplify using `using h v₀`.

Rewrite using `[hset, wtOf_pi, Finset.prod_eq_single v₀]`. Simplify using the standard rewrite rules. Introduce `v _ hv`. Simplify using `[hv, wtOf_univ, hP]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ v₀) h`.
-/
theorem wtOf_one_place (P : Ω → ℝ) (hP : ∑ c, P c = 1) (S : Set Ω) (v₀ : ι) :
    wtOf (fun x : ι → Ω => ∏ v, P (x v)) {x | x v₀ ∈ S} = wtOf P S := by
  have hset : {x : ι → Ω | x v₀ ∈ S} =
      {x : ι → Ω | ∀ v, x v ∈ (if v = v₀ then S else Set.univ)} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h v
      split_ifs with hv
      · subst hv
        exact h
      · exact Set.mem_univ _
    · intro h
      simpa using h v₀
  rw [hset, wtOf_pi, Finset.prod_eq_single v₀]
  · simp
  · intro v _ hv
    simp [hv, wtOf_univ, hP]
  · intro h
    exact absurd (Finset.mem_univ v₀) h

end prod

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Polynomial

/- English proof (translation)
Introduce `K L ι J _ _ _ _ _ _ _ N q₁ d χ P hN hq hq1 hd hne hq2 hd2 hmax h16 hq1d hdd hP0 hP1 hPsq`. Establish `hμ : ∀ x : ι → Fin N → K, 0 ≤ ∏ v, P (x v)` using `fun x => Finset.prod_nonneg fun v _ => hP0 _`. Establish `hconv : ∀ (p : (Fin N → K) → Prop), wtOf P {c | c ∈ sqSet K N ∧ p c} = ∑ c ∈ (sqSet K N).filter p, sqWeight (monicOf c)`. Introduce `p`. Rewrite using `[wtOf_eq_filter']`.

Conclude with `Finset.sum_congr rfl fun c hc => hPsq c (Finset.mem_filter.1 hc).1`. Use `set q : ℝ := (Fintype.card K : ℝ) with hqdef`. Use `set f : ℝ := (Fintype.card ι : ℝ) with hfdef`. Use `set S1 : Set (Fin N → K) := {c | c ∈ sqSet K N}ᶜ with hS1`. Use `set S3 : Set (Fin N → K) := {c | c ∈ sqSet K N ∧ ∃ l : ℕ, l.Prime ∧ l ∉ BB (Fintype.card K) N ∧ ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L)} with hS3`.

Use `set S4 : Kˣ → Set (Fin N → K) := fun c₀ => {c | c ∈ sqSet K N ∧ ∃ l : ℕ, l.Prime ∧ l ≠ Fintype.card K ∧ ∃ x ∈ (monicOf c).rootSet L, primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))} with hS4`. Use `set S5 : ℕ → Set (Fin N → K) := fun a => {c | c ∈ sqSet K N ∧ ∃ h : K[X], h ∣ monicOf c ∧ h.natDegree = a} with hS5`. Use `set S6 : Set (Fin N → K) := {c | c ∈ sqSet K N ∧ ¬ ∃ Q : K[X], Irreducible Q ∧ Q ∣ monicOf c ∧ Q.natDegree.Prime ∧ N < 2 * Q.natDegree ∧ Q.natDegree + 3 ≤ N} with hS6`. Establish `b1 : wtOf P S1 ≤ 2 / q`. Rewrite using `[hS1, wtOf_compl, wtOf_univ, hP1]`.

Establish `e : wtOf P {c | c ∈ sqSet K N} = ∑ c ∈ sqSet K N, sqWeight (monicOf c)`. Use `hconv (fun _ => True)` as an intermediate fact. Simplify using `using this`. Rewrite using `[e]`. Use `h1 K N (by omega)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `b3 : wtOf P S3 ≤ 23 * Real.log q / Real.sqrt q`. Use `(hconv _).trans_le ?_` and prove the remaining obligations. Use `h3 K L N hq` and compare the differences between its conclusion and the goal. Establish `b4 : ∀ c₀ : Kˣ, wtOf P (S4 c₀) ≤ 1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / (q - 1)`.

Introduce `c₀`. Use `(hconv _).trans_le ?_` and prove the remaining obligations. Use `h4 K L N q₁ d c₀ (by omega) hq1 hd hne hq2 hd2 hmax h16 hq1d hdd` and compare the differences between its conclusion and the goal. Establish `b5 : ∀ a ∈ Finset.Icc 1 (N / 2), wtOf P (S5 a) ≤ 7 / 8`. Introduce `a ha`.

Rewrite `ha` using `[Finset.mem_Icc]`. Use `(hconv _).trans_le ?_` and prove the remaining obligations. Use `h5 K N a (by omega) (by omega)` and compare the differences between its conclusion and the goal. Establish `b6 : wtOf P S6 ≤ 1 - 1 / (5 * Real.log N)`. Use `(hconv _).trans_le ?_` and prove the remaining obligations.

Use `h6 K N hN` and compare the differences between its conclusion and the goal. Establish `hcover : {x : ι → Fin N → K | ¬ GoodAt K L N (fun v => monicOf (x v)) χ} ⊆ (((((⋃ v ∈ (Finset.univ : Finset ι), {x : ι → Fin N → K | x v ∈ S1}) ∪ (⋃ v ∈ (Finset.univ : Finset ι), {x : ι → Fin N → K | x v ∈ S3})) ∪ (⋃ w ∈ (Finset.univ : Finset (ι × J)), ({x : ι → Fin N → K | x w.1 …`. Introduce `x hx`. Assume the negation of the conclusion as `hcon`. Simplify using `only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, Set.mem_setOf_eq, Finset.mem_univ, true_implies, forall_true_left] at hcon`.

Take `⟨⟨⟨⟨c1, c3⟩, c4⟩, c5⟩, c6⟩` from `hcon`. Establish `hsq : ∀ v, x v ∈ sqSet K N`. Introduce `v`. Use `c1 v` as an intermediate fact. Simplify `this` using `[hS1]`.

Establish `hsq' : ∀ v, Squarefree (monicOf (x v)) ∧ (monicOf (x v)).coeff 0 ≠ 0`. Introduce `v`. Use `hsq v` as an intermediate fact. Simplify `this` using `[sqSet]`. Apply `hx` to reduce the goal to its premises.

Use `⟨fun v => ⟨monicOf_monic _, monicOf_natDegree _, (hsq' v).2⟩, fun v => (hsq' v).1, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `l hl hlB v`. Assume the negation of the conclusion as `hinj`. Conclude with `c3 v ⟨hsq v, l, hl, hlB, hinj⟩`. Introduce `l hl hlq v j y hy`.

Use `⟨fun he => ?_, fun he => ?_⟩` and prove the remaining obligations. Conclude with `(c4 (v, j)).1 ⟨hsq v, l, hl, hlq, y, hy, he⟩`. Conclude with `(c4 (v, j)).2 ⟨hsq v, l, hl, hlq, y, hy, he⟩`. Introduce `a ha1 ha2`. Assume the negation of the conclusion as `hall`.

Use `push Not at hall`. Conclude with `c5 a (Finset.mem_Icc.2 ⟨ha1, by omega⟩) fun v => ⟨hsq v, hall v⟩`. Assume the negation of the conclusion as `hno push Not at hno`. Apply `c6` to reduce the goal to its premises. Introduce `v`.

Use `⟨hsq v, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨Q, hQ1, hQ2, hQ3, hQ4, hQ5⟩`. Conclude with `absurd hQ5 (not_le.2 (hno v Q hQ1 hQ2 hQ3 hQ4))`. Rewrite using `[← wtOf_eq_filter (fun x : ι → Fin N → K => ∏ v, P (x v)) (fun x => ¬ GoodAt K L N (fun v => monicOf (x v)) χ)]`. Use `(wtOf_mono _ hμ hcover).trans ?_` and prove the remaining obligations.

Use `(wtOf_union_le _ hμ _ _).trans (add_le_add ((wtOf_union_le _ hμ _ _).trans (add_le_add ((wtOf_union_le _ hμ _ _).trans (add_le_add ((wtOf_union_le _ hμ _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)) ?_)` and prove the remaining obligations. Use `(wtOf_biUnion_le _ hμ _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `(wtOf_biUnion_le _ hμ _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Use `(wtOf_biUnion_le _ hμ _ _).trans ?_ set B : ℝ := 1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / (q - 1) with hB` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun w _ => (wtOf_union_le _ hμ _ _).trans (add_le_add ?_ ?_)` and prove the remaining obligations. Rewrite using `[wtOf_one_place P hP1]`. Conclude with `b4 _`.

Rewrite using `[wtOf_one_place P hP1]`. Conclude with `b4 _`. Use `_ = 2 * f * (Fintype.card J : ℝ) * B := by`. Simplify using `[hfdef, Fintype.card_prod]`. Expand and normalize the polynomial expressions, which then agree.

Use `(wtOf_biUnion_le _ hμ _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun a ha => ?_` and prove the remaining obligations. Rewrite using `[wtOf_pi P (fun _ => S5 a), Finset.prod_const, Finset.card_univ]`. Conclude with `pow_le_pow_left₀ (wtOf_nonneg P hP0 _) (b5 a ha) _`.

Use `_ = ((N / 2 : ℕ) : ℝ) * (7 / 8 : ℝ) ^ Fintype.card ι := by simp`. Use `_ ≤ (N : ℝ) / 2 * (7 / 8 : ℝ) ^ Fintype.card ι := by`. Use `mul_le_mul_of_nonneg_right ?_ (by positivity)` and prove the remaining obligations. Conclude with `Nat.cast_div_le`. Rewrite using `[wtOf_pi P (fun _ => S6), Finset.prod_const, Finset.card_univ]`.

Combine the equalities or inequalities in the displayed calculation. Use `pow_le_pow_left₀ (wtOf_nonneg P hP0 _) (b6.trans ?_) _` and prove the remaining obligations. Conclude with `Real.one_sub_le_exp_neg _`. Use `_ = Real.exp (-f / (5 * Real.log N)) := by`. Rewrite using `[← Real.exp_nat_mul]`.

Use `congr 1`. Rewrite using `[hfdef]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem propW_of (h1 : SqMassLower) (h3 : LocalEstimateII) (h4 : LocalEstimateIII)
    (h5 : LocalEstimateIV) (h6 : LocalEstimateV) : PropW := by
  classical
  intro K L ι J _ _ _ _ _ _ _ N q₁ d χ P hN hq hq1 hd hne hq2 hd2 hmax h16 hq1d hdd hP0 hP1 hPsq
  have hμ : ∀ x : ι → Fin N → K, 0 ≤ ∏ v, P (x v) :=
    fun x => Finset.prod_nonneg fun v _ => hP0 _
  have hconv : ∀ (p : (Fin N → K) → Prop), wtOf P {c | c ∈ sqSet K N ∧ p c} =
      ∑ c ∈ (sqSet K N).filter p, sqWeight (monicOf c) := by
    intro p
    rw [wtOf_eq_filter']
    exact Finset.sum_congr rfl fun c hc => hPsq c (Finset.mem_filter.1 hc).1
  set q : ℝ := (Fintype.card K : ℝ) with hqdef
  set f : ℝ := (Fintype.card ι : ℝ) with hfdef

  set S1 : Set (Fin N → K) := {c | c ∈ sqSet K N}ᶜ with hS1
  set S3 : Set (Fin N → K) := {c | c ∈ sqSet K N ∧ ∃ l : ℕ, l.Prime ∧
    l ∉ BB (Fintype.card K) N ∧ ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L)} with hS3
  set S4 : Kˣ → Set (Fin N → K) := fun c₀ => {c | c ∈ sqSet K N ∧ ∃ l : ℕ, l.Prime ∧
    l ≠ Fintype.card K ∧ ∃ x ∈ (monicOf c).rootSet L,
      primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))} with hS4
  set S5 : ℕ → Set (Fin N → K) := fun a => {c | c ∈ sqSet K N ∧
    ∃ h : K[X], h ∣ monicOf c ∧ h.natDegree = a} with hS5
  set S6 : Set (Fin N → K) := {c | c ∈ sqSet K N ∧ ¬ ∃ Q : K[X], Irreducible Q ∧ Q ∣ monicOf c ∧
    Q.natDegree.Prime ∧ N < 2 * Q.natDegree ∧ Q.natDegree + 3 ≤ N} with hS6

  have b1 : wtOf P S1 ≤ 2 / q := by
    rw [hS1, wtOf_compl, wtOf_univ, hP1]
    have e : wtOf P {c | c ∈ sqSet K N} = ∑ c ∈ sqSet K N, sqWeight (monicOf c) := by
      have := hconv (fun _ => True)
      simpa using this
    rw [e]
    have := h1 K N (by omega)
    linarith
  have b3 : wtOf P S3 ≤ 23 * Real.log q / Real.sqrt q := by
    refine (hconv _).trans_le ?_
    convert h3 K L N hq
  have b4 : ∀ c₀ : Kˣ, wtOf P (S4 c₀) ≤
      1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / (q - 1) := by
    intro c₀
    refine (hconv _).trans_le ?_
    convert h4 K L N q₁ d c₀ (by omega) hq1 hd hne hq2 hd2 hmax h16 hq1d hdd
  have b5 : ∀ a ∈ Finset.Icc 1 (N / 2), wtOf P (S5 a) ≤ 7 / 8 := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    refine (hconv _).trans_le ?_
    convert h5 K N a (by omega) (by omega)
  have b6 : wtOf P S6 ≤ 1 - 1 / (5 * Real.log N) := by
    refine (hconv _).trans_le ?_
    convert h6 K N hN

  have hcover : {x : ι → Fin N → K | ¬ GoodAt K L N (fun v => monicOf (x v)) χ} ⊆
      (((((⋃ v ∈ (Finset.univ : Finset ι), {x : ι → Fin N → K | x v ∈ S1}) ∪
        (⋃ v ∈ (Finset.univ : Finset ι), {x : ι → Fin N → K | x v ∈ S3})) ∪
        (⋃ w ∈ (Finset.univ : Finset (ι × J)), ({x : ι → Fin N → K | x w.1 ∈ S4 (χ w.1 w.2)} ∪
          {x : ι → Fin N → K | x w.1 ∈ S4 (χ w.1 w.2)⁻¹}))) ∪
        (⋃ a ∈ Finset.Icc 1 (N / 2), {x : ι → Fin N → K | ∀ v, x v ∈ S5 a})) ∪
        {x : ι → Fin N → K | ∀ v, x v ∈ S6}) := by
    intro x hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, Set.mem_setOf_eq,
      Finset.mem_univ, true_implies, forall_true_left] at hcon
    obtain ⟨⟨⟨⟨c1, c3⟩, c4⟩, c5⟩, c6⟩ := hcon
    have hsq : ∀ v, x v ∈ sqSet K N := by
      intro v
      have := c1 v
      simpa [hS1] using this
    have hsq' : ∀ v, Squarefree (monicOf (x v)) ∧ (monicOf (x v)).coeff 0 ≠ 0 := by
      intro v
      have := hsq v
      simpa [sqSet] using this
    apply hx
    refine ⟨fun v => ⟨monicOf_monic _, monicOf_natDegree _, (hsq' v).2⟩, fun v => (hsq' v).1,
      ?_, ?_, ?_, ?_⟩
    · intro l hl hlB v
      by_contra hinj
      exact c3 v ⟨hsq v, l, hl, hlB, hinj⟩
    · intro l hl hlq v j y hy
      refine ⟨fun he => ?_, fun he => ?_⟩
      · exact (c4 (v, j)).1 ⟨hsq v, l, hl, hlq, y, hy, he⟩
      · exact (c4 (v, j)).2 ⟨hsq v, l, hl, hlq, y, hy, he⟩
    · intro a ha1 ha2
      by_contra hall
      push Not at hall
      exact c5 a (Finset.mem_Icc.2 ⟨ha1, by omega⟩) fun v => ⟨hsq v, hall v⟩
    · by_contra hno
      push Not at hno
      apply c6
      intro v
      refine ⟨hsq v, ?_⟩
      rintro ⟨Q, hQ1, hQ2, hQ3, hQ4, hQ5⟩
      exact absurd hQ5 (not_le.2 (hno v Q hQ1 hQ2 hQ3 hQ4))
  rw [← wtOf_eq_filter (fun x : ι → Fin N → K => ∏ v, P (x v))
    (fun x => ¬ GoodAt K L N (fun v => monicOf (x v)) χ)]
  refine (wtOf_mono _ hμ hcover).trans ?_
  refine (wtOf_union_le _ hμ _ _).trans (add_le_add ((wtOf_union_le _ hμ _ _).trans
    (add_le_add ((wtOf_union_le _ hμ _ _).trans (add_le_add ((wtOf_union_le _ hμ _ _).trans
      (add_le_add ?_ ?_)) ?_)) ?_)) ?_)
  · refine (wtOf_biUnion_le _ hμ _ _).trans ?_
    calc ∑ v : ι, wtOf (fun x : ι → Fin N → K => ∏ v, P (x v)) {x | x v ∈ S1}
        = ∑ _v : ι, wtOf P S1 := Finset.sum_congr rfl fun v _ => wtOf_one_place P hP1 S1 v
      _ = f * wtOf P S1 := by simp [hfdef]
      _ ≤ f * (2 / q) := mul_le_mul_of_nonneg_left b1 (Nat.cast_nonneg _)
      _ = 2 * f / q := by ring
  · refine (wtOf_biUnion_le _ hμ _ _).trans ?_
    calc ∑ v : ι, wtOf (fun x : ι → Fin N → K => ∏ v, P (x v)) {x | x v ∈ S3}
        = ∑ _v : ι, wtOf P S3 := Finset.sum_congr rfl fun v _ => wtOf_one_place P hP1 S3 v
      _ = f * wtOf P S3 := by simp [hfdef]
      _ ≤ f * (23 * Real.log q / Real.sqrt q) :=
          mul_le_mul_of_nonneg_left b3 (Nat.cast_nonneg _)
      _ = 23 * f * Real.log q / Real.sqrt q := by ring
  · refine (wtOf_biUnion_le _ hμ _ _).trans ?_
    set B : ℝ := 1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / (q - 1) with hB
    calc ∑ w : ι × J, wtOf (fun x : ι → Fin N → K => ∏ v, P (x v))
          ({x | x w.1 ∈ S4 (χ w.1 w.2)} ∪ {x | x w.1 ∈ S4 (χ w.1 w.2)⁻¹})
        ≤ ∑ _w : ι × J, (B + B) := by
          refine Finset.sum_le_sum fun w _ => (wtOf_union_le _ hμ _ _).trans (add_le_add ?_ ?_)
          · rw [wtOf_one_place P hP1]; exact b4 _
          · rw [wtOf_one_place P hP1]; exact b4 _
      _ = 2 * f * (Fintype.card J : ℝ) * B := by
          simp [hfdef, Fintype.card_prod]; ring
  · refine (wtOf_biUnion_le _ hμ _ _).trans ?_
    calc ∑ a ∈ Finset.Icc 1 (N / 2), wtOf (fun x : ι → Fin N → K => ∏ v, P (x v))
          {x | ∀ v, x v ∈ S5 a}
        ≤ ∑ _a ∈ Finset.Icc 1 (N / 2), (7 / 8 : ℝ) ^ Fintype.card ι := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [wtOf_pi P (fun _ => S5 a), Finset.prod_const, Finset.card_univ]
          exact pow_le_pow_left₀ (wtOf_nonneg P hP0 _) (b5 a ha) _
      _ = ((N / 2 : ℕ) : ℝ) * (7 / 8 : ℝ) ^ Fintype.card ι := by simp
      _ ≤ (N : ℝ) / 2 * (7 / 8 : ℝ) ^ Fintype.card ι := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Nat.cast_div_le
  · rw [wtOf_pi P (fun _ => S6), Finset.prod_const, Finset.card_univ]
    calc wtOf P S6 ^ Fintype.card ι ≤ (Real.exp (-(1 / (5 * Real.log N)))) ^ Fintype.card ι := by
          refine pow_le_pow_left₀ (wtOf_nonneg P hP0 _) (b6.trans ?_) _
          exact Real.one_sub_le_exp_neg _
      _ = Real.exp (-f / (5 * Real.log N)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          rw [hfdef]; ring

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Conclude with `prop1FromCount_of dyadic_window_bound excluded_set_simplification proposition_one_central_count`.
-/
theorem proposition_one_from_count : Prop1FromCount := by
  exact prop1FromCount_of dyadic_window_bound excluded_set_simplification proposition_one_central_count

/- English proof (translation)
Conclude with `localEstimateIV_of h subsum_bound divisor_degree_subsum`.
-/
theorem localEstimateIV_of_typeSetWeight (h : TypeSetWeight) : LocalEstimateIV := by
  exact localEstimateIV_of h subsum_bound divisor_degree_subsum

/- English proof (translation)
Conclude with `localEstimateV_of h prime_cycle_probability_sum prime_reciprocal_sum_bound`.
-/
theorem localEstimateV_of_typeSetWeight (h : TypeSetWeight) : LocalEstimateV := by
  exact localEstimateV_of h prime_cycle_probability_sum prime_reciprocal_sum_bound

/- English proof (translation)
Conclude with `sqMassLeOne_of type_set_weight_bound`.
-/
theorem square_mass_le_one : SqMassLeOne := by
  exact sqMassLeOne_of type_set_weight_bound

/- English proof (translation)
Conclude with `divisorBound_of square_mass_le_one`.
-/
theorem divisor_weight_bound : DivisorBound := by
  exact divisorBound_of square_mass_le_one

/- English proof (translation)
Conclude with `localEstimateIV_of_typeSetWeight type_set_weight_bound`.
-/
theorem local_estimate_fourth : LocalEstimateIV := by
  exact localEstimateIV_of_typeSetWeight type_set_weight_bound

/- English proof (translation)
Conclude with `localEstimateV_of_typeSetWeight type_set_weight_bound`.
-/
theorem local_estimate_fifth : LocalEstimateV := by
  exact localEstimateV_of_typeSetWeight type_set_weight_bound

/- English proof (translation)
Conclude with `propW_of square_mass_lower_bound h3 h4 local_estimate_fourth local_estimate_fifth`.
-/
theorem propW_of_localEstimates (h3 : LocalEstimateII) (h4 : LocalEstimateIII) : PropW := by
  exact propW_of square_mass_lower_bound h3 h4 local_estimate_fourth local_estimate_fifth

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
