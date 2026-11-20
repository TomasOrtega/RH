import Formalism.LandauZeroFreeBounds.NoZeroComplexOf

open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Establish `hp1 : (1 : ℝ) ≤ p` using `by linarith`. Establish `hp0 : (p : ℂ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hw : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re)`. Rewrite using `[Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]`.

Establish `hx : (p : ℝ) ^ (-s.re) ≤ 1 / 2`. Establish `h1 : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)`. Rewrite `h1` using `[Real.rpow_neg_one]`. Establish `h2 : (p : ℝ)⁻¹ ≤ 1 / 2`. Rewrite using `[inv_eq_one_div]`.

Conclude with `one_div_le_one_div_of_le (by norm_num) hp2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx0 : 0 ≤ (p : ℝ) ^ (-s.re)` using `Real.rpow_nonneg (by linarith) _`. Establish `hden : 1 / 2 ≤ ‖1 - (p : ℂ) ^ (-s)‖`. Use `norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))` as an intermediate fact.

Rewrite `this` using `[norm_one, hw]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hne : (1 - (p : ℂ) ^ (-s)) ≠ 0`. Introduce `h`. Rewrite `hden` using `[h, norm_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hder : HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p) s`. Establish `h1 : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p * (-1)) s` using `(hasDerivAt_id s).neg.const_cpow (Or.inl hp0)`. Establish `h2` using `(hasDerivAt_const s (1 : ℂ)).sub h1`. Conclude with `h2.congr_deriv (by ring)`.

Use `⟨hne, hder.differentiableAt, ?_⟩` and prove the remaining obligations. Establish `hL : 0 ≤ Real.log p` using `Real.log_nonneg hp1`. Establish `hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ)` using `Complex.natCast_log.symm`. Rewrite using `[logDeriv_apply, hder.deriv, norm_div, norm_mul, hw, hlog, Complex.norm_of_nonneg hL]`. Establish `hdpos : 0 < ‖1 - (p : ℂ) ^ (-s)‖` using `by linarith`.

Rewrite using `[div_le_iff₀ hdpos]`. Establish `hxd : (p : ℝ) ^ (-s.re) ≤ ‖1 - (p : ℂ) ^ (-s)‖` using `by linarith`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hxd hL]`.
-/
lemma euler_factor_logDeriv_bound (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 1 < s.re) :
    (1 - (p : ℂ) ^ (-s)) ≠ 0 ∧ DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s ∧
    ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤ Real.log p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hw : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  have hx : (p : ℝ) ^ (-s.re) ≤ 1 / 2 := by
    have h1 : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    rw [Real.rpow_neg_one] at h1
    have h2 : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hx0 : 0 ≤ (p : ℝ) ^ (-s.re) := Real.rpow_nonneg (by linarith) _
  have hden : 1 / 2 ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
    rw [norm_one, hw] at this
    linarith
  have hne : (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hden
    linarith
  have hder : HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z))
      ((p : ℂ) ^ (-s) * Complex.log p) s := by
    have h1 : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p * (-1)) s :=
      (hasDerivAt_id s).neg.const_cpow (Or.inl hp0)
    have h2 := (hasDerivAt_const s (1 : ℂ)).sub h1
    exact h2.congr_deriv (by ring)
  refine ⟨hne, hder.differentiableAt, ?_⟩
  have hL : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := Complex.natCast_log.symm
  rw [logDeriv_apply, hder.deriv, norm_div, norm_mul, hw, hlog, Complex.norm_of_nonneg hL]
  have hdpos : 0 < ‖1 - (p : ℂ) ^ (-s)‖ := by linarith
  rw [div_le_iff₀ hdpos]
  have hxd : (p : ℝ) ^ (-s.re) ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hxd hL]

/- English proof (translation)
Establish `hs1 : s ≠ 1`. Introduce and unpack `rfl`. Simplify using `at hs`. Establish `hfac : ∀ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)) ≠ 0 ∧ DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s ∧ ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤ Real.log p` using `fun p hp => euler_factor_logDeriv_bound p (Nat.prime_of_mem_primeFactors hp) s hs`. Establish `heq : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 s] fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z` using `by filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz`.

Conclude with `DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) (Set.mem_compl_singleton_iff.mp hz)`. Establish `hPne : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun p hp => (hfac p hp).1`. Establish `hPd : DifferentiableAt ℂ (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s` using `DifferentiableAt.fun_finsetProd fun p hp => (hfac p hp).2.1`. Establish `hζ : riemannZeta s ≠ 0` using `riemannZeta_ne_zero_of_one_lt_re hs`. Establish `hζd : DifferentiableAt ℂ riemannZeta s` using `differentiableAt_riemannZeta hs1`.

Establish `hmul : logDeriv (fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z) s = logDeriv (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s + logDeriv riemannZeta s` using `logDeriv_mul (f := fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) (g := riemannZeta) s hPne hζ hPd hζd`. Establish `hprod : logDeriv (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s = ∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s` using `logDeriv_prod (f := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z)) (fun p hp => (hfac p hp).1) (fun p hp => (hfac p hp).2.1)`. Establish `hneg : negLD (1 : DirichletCharacter ℂ q) s = -(logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s)` using `rfl`. Establish `hS : ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤ Real.log q`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Real.log_prod]`. Introduce `p hp`. Conclude with `(Nat.prime_of_mem_primeFactors hp).ne_zero` after adjusting the coercions. Use `_ ≤ Real.log q := by`. Apply `Real.log_le_log` to reduce the goal to its premises.

Conclude with `Finset.prod_pos fun p hp => by`. Conclude with `(Nat.prime_of_mem_primeFactors hp).pos` after adjusting the coercions. Rewrite using `[← Nat.cast_prod]`. Conclude with `Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.prod_primeFactors_dvd q)` after adjusting the coercions. Establish `hre` using `RCLike.abs_re_le_norm (∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s)`.

Establish `hre'` using `neg_abs_le (∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s).re`. Rewrite using `[hneg, (logDeriv_congr_nhds heq).eq_of_nhds, hmul, hprod, logDeriv_apply]`. Simplify using `only [Complex.neg_re, Complex.add_re]`. Simplify using `only [RCLike.re_to_complex] at hre`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma re_negLogDeriv_le (q : ℕ) [NeZero q] (s : ℂ) (hs : 1 < s.re) :
    (negLD (1 : DirichletCharacter ℂ q) s).re ≤
      (-(deriv riemannZeta s / riemannZeta s)).re + Real.log q := by
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs
  have hfac : ∀ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)) ≠ 0 ∧
      DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s ∧
      ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤ Real.log p :=
    fun p hp => euler_factor_logDeriv_bound p (Nat.prime_of_mem_primeFactors hp) s hs
  have heq : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 s]
      fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q)
      (Set.mem_compl_singleton_iff.mp hz)
  have hPne : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => (hfac p hp).1
  have hPd : DifferentiableAt ℂ (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s :=
    DifferentiableAt.fun_finsetProd fun p hp => (hfac p hp).2.1
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hζd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hmul : logDeriv (fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z) s =
      logDeriv (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s +
        logDeriv riemannZeta s :=
    logDeriv_mul (f := fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z)))
      (g := riemannZeta) s hPne hζ hPd hζd
  have hprod : logDeriv (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s =
      ∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s :=
    logDeriv_prod (f := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z))
      (fun p hp => (hfac p hp).1) (fun p hp => (hfac p hp).2.1)
  have hneg : negLD (1 : DirichletCharacter ℂ q) s =
      -(logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s) := rfl
  have hS : ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤
      Real.log q := by
    calc ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖
        ≤ ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ :=
          norm_sum_le _ _
      _ ≤ ∑ p ∈ q.primeFactors, Real.log p := Finset.sum_le_sum fun p hp => (hfac p hp).2.2
      _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      _ ≤ Real.log q := by
          apply Real.log_le_log
          · exact Finset.prod_pos fun p hp => by
              exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
          · rw [← Nat.cast_prod]
            exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q))
              (Nat.prod_primeFactors_dvd q)
  have hre := RCLike.abs_re_le_norm
    (∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s)
  have hre' := neg_abs_le
    (∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s).re
  rw [hneg, (logDeriv_congr_nhds heq).eq_of_nhds, hmul, hprod, logDeriv_apply]
  simp only [Complex.neg_re, Complex.add_re]
  simp only [RCLike.re_to_complex] at hre
  linarith

end Formalism.ZeroFreeDirichlet
