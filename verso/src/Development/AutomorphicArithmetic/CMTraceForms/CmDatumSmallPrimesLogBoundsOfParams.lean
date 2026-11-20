import Mathlib
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
import Development.AutomorphicArithmetic.CMTraceForms.SumLogPrimeFactorsMulTwoAddLogbLe

open NumberField Formalism.BasicNotions Formalism.HC

/- English proof (translation)
Introduce `D L P`. Establish `hx : 0 < L.sc.x` using `lt_trans one_pos L.sc.one_lt_alt`. Establish `hy : 1 ≤ L.sc.x ^ (L.sc.eps / 4)` using `Real.one_le_rpow L.sc.one_lt_alt.le (by have := L.sc.eps_pos; positivity)`. Establish `hQ0 : 0 < D.host.QS` using `D.host.QS_pos`. Establish `hQn : D.host.QS ≤ D.R.n ^ 2` using `D.host.QS_le`.

Establish `hnN : D.R.n ≤ D.R.N D.R.m`. Use `D.R.f_le_k` as an intermediate fact. Unfold `Ranks.n Ranks.N`. Use linear arithmetic over natural numbers and integers. Establish `hm : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10`.

Establish `: (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (le_trans one_le_two D.R.two_le_m)`. Conclude with `one_le_pow₀ this`. Establish `hN : (D.R.n : ℝ) ≤ (D.s.Del : ℝ)`. Establish `h1 : (D.R.n : ℝ) ≤ (D.R.N D.R.m : ℝ)` using `by exact_mod_cast hnN`. Establish `h2` using `P.Del_ge.2.2.2`.

Establish `h3 : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10` using `le_mul_of_one_le_right (Nat.cast_nonneg _) hm`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn0 : (0 : ℝ) < D.R.n`. Establish `: 0 < D.R.n`. Break down `Nat.eq_zero_or_pos D.R.n with h | h` into its components or cases.

Rewrite `hQn` using `[h]`. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Conclude with `this` after adjusting the coercions. Establish `hlog : Real.log D.host.QS ≤ L.sc.x ^ (L.sc.eps / 4)`.

Establish `h1 : Real.log D.host.QS ≤ Real.log ((D.R.n : ℝ) ^ 2)` using `Real.log_le_log (by exact_mod_cast hQ0) (by exact_mod_cast hQn)`. Rewrite `h1` using `[Real.log_pow]`. Establish `h2` using `Real.log_le_log hn0 hN`. Establish `h3` using `P.logDel`. Move the coercions through the operations in `at h1`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨?_, hlog⟩` and prove the remaining obligations. Establish `h4 : (L.sc.x ^ (L.sc.eps / 4)) ^ 4 = L.sc.L`. Unfold `Scale.L`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hx.le]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `UpperTheory.sum_log_primeFactors_mul_two_add_logb_le D.host.QS _ hQ0.ne' hy hlog` as an intermediate fact. Rewrite `this` using `[h4]`.

Conclude with `this`.
-/
theorem UpperTheory.cmDatum_smallPrimes_log_bounds_of_params :
    ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L →
      (∑ p ∈ D.host.small, Real.log (p : ℝ)) * (2 + Real.logb 2 D.host.QS) ≤ 11 * L.sc.L ∧ Real.log D.host.QS ≤ L.sc.x ^ (L.sc.eps / 4) := by
  intro D L P
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hy : 1 ≤ L.sc.x ^ (L.sc.eps / 4) :=
    Real.one_le_rpow L.sc.one_lt_alt.le (by have := L.sc.eps_pos; positivity)
  have hQ0 : 0 < D.host.QS := D.host.QS_pos
  have hQn : D.host.QS ≤ D.R.n ^ 2 := D.host.QS_le
  have hnN : D.R.n ≤ D.R.N D.R.m := by
    have := D.R.f_le_k
    unfold Ranks.n Ranks.N
    omega
  have hm : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := by
    have : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (le_trans one_le_two D.R.two_le_m)
    exact one_le_pow₀ this
  have hN : (D.R.n : ℝ) ≤ (D.s.Del : ℝ) := by
    have h1 : (D.R.n : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hnN
    have h2 := P.Del_ge.2.2.2
    have h3 : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) hm
    linarith
  have hn0 : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := by
      rcases Nat.eq_zero_or_pos D.R.n with h | h
      · rw [h] at hQn; omega
      · exact h
    exact_mod_cast this
  have hlog : Real.log D.host.QS ≤ L.sc.x ^ (L.sc.eps / 4) := by
    have h1 : Real.log D.host.QS ≤ Real.log ((D.R.n : ℝ) ^ 2) :=
      Real.log_le_log (by exact_mod_cast hQ0) (by exact_mod_cast hQn)
    rw [Real.log_pow] at h1
    have h2 := Real.log_le_log hn0 hN
    have h3 := P.logDel
    push_cast at h1
    linarith
  refine ⟨?_, hlog⟩
  have h4 : (L.sc.x ^ (L.sc.eps / 4)) ^ 4 = L.sc.L := by
    unfold Scale.L
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    ring
  have := UpperTheory.sum_log_primeFactors_mul_two_add_logb_le D.host.QS _ hQ0.ne' hy hlog
  rw [h4] at this
  exact this
