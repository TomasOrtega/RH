import Formalism.LandauZeroFreeBounds.NoZeroComplexOf

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (authored)
The norm of p raised to −s is the power with real exponent minus the real part of s. Since p > 1 and this exponent is negative, its norm is less than one, so it cannot equal one.
-/
lemma one_sub_prime_cpow_neg_ne_zero (p : ℕ) (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.1 h).symm
  have h2 := congrArg norm h1
  rw [norm_natCast_cpow_of_pos hp.pos, norm_one, neg_re] at h2
  have h3 : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  linarith

/- English proof (authored)
Away from one the principal-character L-function is zeta times the finite product of removed Euler factors. Every factor is nonzero for positive real part, so if the product with zeta vanishes, zeta must vanish.
-/
theorem trivialCharZerosOfZeta : TrivZeros := by
  intro q _ s hs hs1 h0
  have hmul := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hs1
  have h0' : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s = 0 := by
    rw [← hmul]
    exact h0
  rcases mul_eq_zero.1 h0' with h | h
  · exfalso
    obtain ⟨p, hp, hp0⟩ := Finset.prod_eq_zero_iff.1 h
    exact one_sub_prime_cpow_neg_ne_zero p (Nat.prime_of_mem_primeFactors hp) hs hp0
  · exact h

/- English proof (authored)
At a unit the quadratic identity forces the character value to be one or minus one, and both are fixed by conjugation. At a nonunit the value is zero, which is fixed as well.
-/
lemma conj_apply_of_sq_eq_one {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (a : ZMod q) :
    starRingEnd ℂ (χ a) = χ a := by
  by_cases ha : IsUnit a
  · have h2 : χ a * χ a = 1 := by
      rw [← sq, ← MulChar.pow_apply' χ two_ne_zero, hχ, MulChar.one_apply ha]
    rcases mul_self_eq_one_iff.1 h2 with h | h
    · rw [h, map_one]
    · rw [h, map_neg, map_one]
  · rw [MulChar.map_nonunit χ ha, map_zero]

/- English proof (authored)
Both arguments lie to the right of one, so use their convergent Dirichlet series. Conjugation commutes with the sum. The character coefficients are fixed, and conjugation of the complex power of each positive index conjugates its exponent. Conjugating the argument twice restores each original term.
-/
lemma conj_LFunction_conj_of_sq_eq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    (z : ℂ) (hz : 1 < z.re) :
    starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z)) =
      DirichletCharacter.LFunction χ z := by
  have hz' : 1 < (starRingEnd ℂ z).re := by rwa [Complex.conj_re]
  rw [DirichletCharacter.LFunction_eq_LSeries χ hz', DirichletCharacter.LFunction_eq_LSeries χ hz,
    LSeries, LSeries, Complex.conj_tsum]
  congr 1
  funext m
  rw [LSeries.term_def, LSeries.term_def]
  split_ifs with hm
  · exact map_zero _
  · show starRingEnd ℂ (χ m / (m : ℂ) ^ starRingEnd ℂ z) = χ m / (m : ℂ) ^ z
    have harg : (m : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact Real.pi_ne_zero.symm
    rw [map_div₀, conj_apply_of_sq_eq_one χ hχ, Complex.cpow_conj _ _ harg, map_natCast (starRingEnd ℂ) m,
      Complex.conj_conj]

/- English proof (authored)
For a nonprincipal character the L-function is entire, as is the function obtained by conjugating both its argument and its value. Their Dirichlet series show equality to the right of one. The identity theorem extends equality to all complex arguments. Evaluating at the conjugate argument gives the stated relation.
-/
theorem realCharConj : RealConj := by
  intro q _ χ hχ h1 s
  have hL : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction h1
  have hG : Differentiable ℂ
      (fun z => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z))) := by
    intro z
    have := (hL (starRingEnd ℂ z)).conj_conj
    rw [Complex.conj_conj] at this
    exact this
  have heq : (fun z => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z))) =
      DirichletCharacter.LFunction χ := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2) (analyticOnNhd_univ_iff_differentiable.2 hG)
      (analyticOnNhd_univ_iff_differentiable.2 hL) ?_
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact conj_LFunction_conj_of_sq_eq_one χ hχ z hz
  have := congrFun heq (starRingEnd ℂ s)
  simp only [Complex.conj_conj] at this
  exact this.symm

end Formalism.ZeroFreeDirichlet
