import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivRiemannZetaLocalZeroSumStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.PrincipalLogDeriv

/- English proof (translation)
Establish `hp1 : (1 : ℝ) ≤ p` using `by exact_mod_cast hp.one_lt.le`. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Rewrite using `[Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma norm_cpow_neg_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  calc (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = 1 / p := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2

/- English proof (translation)
Establish `h` using `norm_cpow_neg_le hp hs`. Establish `h'` using `norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))`. Rewrite `h'` using `[norm_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma half_le_norm_one_sub {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    1 / 2 ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
  have h := norm_cpow_neg_le hp hs
  have h' := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
  rw [norm_one] at h'
  linarith

/- English proof (translation)
Introduce `h`. Establish `h'` using `half_le_norm_one_sub hp hs`. Rewrite `h'` using `[h, norm_zero]`. Evaluate the numerical expressions using `at h'`.
-/
lemma one_sub_ne_zero {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h' := half_le_norm_one_sub hp hs
  rw [h, norm_zero] at h'
  norm_num at h'

/- English proof (translation)
Establish `hc : (p : ℂ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `h : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p * (-1)) s` using `((hasDerivAt_id' s).neg).const_cpow (Or.inl hc)`. Establish `h2 : HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) (-((p : ℂ) ^ (-s) * Complex.log p * (-1))) s` using `h.const_sub 1`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hasDerivAt_factor {p : ℕ} (hp : p.Prime) (s : ℂ) :
    HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p) s := by
  have hc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p * (-1)) s :=
    ((hasDerivAt_id' s).neg).const_cpow (Or.inl hc)
  have h2 : HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z))
      (-((p : ℂ) ^ (-s) * Complex.log p * (-1))) s := h.const_sub 1
  convert h2 using 1
  ring

/- English proof (translation)
Establish `h1` using `norm_cpow_neg_le hp hs`. Establish `h2` using `half_le_norm_one_sub hp hs`. Establish `hl : 0 ≤ Real.log p` using `Real.log_nonneg (by exact_mod_cast hp.one_lt.le)`. Establish `hlog : ‖Complex.log (p : ℂ)‖ = Real.log p`. Rewrite using `[← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p), Complex.norm_real, Real.norm_of_nonneg hl]`.

Rewrite using `[logDeriv_apply, (hasDerivAt_factor hp s).deriv, norm_div, norm_mul, hlog, div_le_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma norm_logDeriv_factor_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤ Real.log p := by
  have h1 := norm_cpow_neg_le hp hs
  have h2 := half_le_norm_one_sub hp hs
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hlog : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p), Complex.norm_real,
      Real.norm_of_nonneg hl]
  rw [logDeriv_apply, (hasDerivAt_factor hp s).deriv, norm_div, norm_mul, hlog,
    div_le_iff₀ (by linarith)]
  nlinarith

/- English proof (translation)
Establish `hq : 0 < q` using `Nat.pos_of_ne_zero (NeZero.ne q)`. Rewrite using `[← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]`. Apply `Real.log_le_log` to reduce the goal to its premises. Conclude with `Finset.prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos`. Establish `h` using `Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)`.

Rewrite using `[← Nat.cast_prod]`. Conclude with `h` after adjusting the coercions.
-/
lemma sum_log_primeFactors_le (q : ℕ) [NeZero q] :
    ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  apply Real.log_le_log
  · exact Finset.prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  · have h := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
    rw [← Nat.cast_prod]
    exact_mod_cast h

/- English proof (translation)
Establish `hs1 : s ≠ 1`. Introduce `h`. Rewrite `hs` using `[h, Complex.one_re]`. Conclude with `lt_irrefl _ hs`. Establish `hre : 1 ≤ s.re` using `hs.le`.

Establish `hev : LFunction (1 : DirichletCharacter ℂ q) =ᶠ[nhds s] fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z` using `by filter_upwards [isOpen_ne.mem_nhds hs1] with z hz`. Conclude with `LFunctionTrivChar_eq_mul_riemannZeta hz`. Establish `hfac : ∀ p ∈ q.primeFactors, (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s ≠ 0` using `fun p hp => one_sub_ne_zero (Nat.prime_of_mem_primeFactors hp) hre`. Establish `hdfac : ∀ p ∈ q.primeFactors, DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s` using `fun p hp => (hasDerivAt_factor (Nat.prime_of_mem_primeFactors hp) s).differentiableAt`. Establish `hF0 : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0` using `Finset.prod_ne_zero_iff.mpr hfac`.

Establish `hFd : DifferentiableAt ℂ (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s` using `DifferentiableAt.fun_finsetProd hdfac`. Establish `hζ0 : riemannZeta s ≠ 0` using `riemannZeta_ne_zero_of_one_lt_re hs`. Establish `hζd : DifferentiableAt ℂ riemannZeta s` using `differentiableAt_riemannZeta hs1`. Establish `hL : deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s = logDeriv (fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z) s`. Rewrite using `[logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]`.

Rewrite using `[hL, logDeriv_mul (f := fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s hF0 hζ0 hFd hζd, ← logDeriv_apply riemannZeta, add_sub_cancel_right, logDeriv_prod (f := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z)) hfac hdfac]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma norm_logDeriv_sub_le (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s
      - deriv riemannZeta s / riemannZeta s‖ ≤ Real.log q := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact lt_irrefl _ hs
  have hre : 1 ≤ s.re := hs.le
  have hev : LFunction (1 : DirichletCharacter ℂ q) =ᶠ[nhds s]
      fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
    exact LFunctionTrivChar_eq_mul_riemannZeta hz
  have hfac : ∀ p ∈ q.primeFactors, (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s ≠ 0 :=
    fun p hp => one_sub_ne_zero (Nat.prime_of_mem_primeFactors hp) hre
  have hdfac : ∀ p ∈ q.primeFactors, DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s :=
    fun p hp => (hasDerivAt_factor (Nat.prime_of_mem_primeFactors hp) s).differentiableAt
  have hF0 : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfac
  have hFd : DifferentiableAt ℂ (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s :=
    DifferentiableAt.fun_finsetProd hdfac
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hζd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hL : deriv (LFunction (1 : DirichletCharacter ℂ q)) s /
      LFunction (1 : DirichletCharacter ℂ q) s =
      logDeriv (fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z) s := by
    rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hL, logDeriv_mul (f := fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s hF0 hζ0
    hFd hζd, ← logDeriv_apply riemannZeta, add_sub_cancel_right,
    logDeriv_prod (f := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z)) hfac hdfac]
  calc ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖
      ≤ ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ q.primeFactors, Real.log p :=
        Finset.sum_le_sum fun p hp => norm_logDeriv_factor_le (Nat.prime_of_mem_primeFactors hp) hre
    _ ≤ Real.log q := sum_log_primeFactors_le q

/- English proof (translation)
Take `⟨C, hC, hZ⟩` from `GlobalTheory.T.logDeriv_riemannZeta_local_zero_sum`. Use `⟨C + 1, by linarith, ?_⟩` and prove the remaining obligations. Introduce `q _ σ t hσ1 hσ2`. Use `set s : ℂ := (σ : ℂ) + t * I with hsdef`. Establish `hsre : s.re = σ` using `by simp [hsdef]`.

Establish `hs1 : 1 < s.re` using `by rw [hsre]; exact hσ1`. Establish `hsne : s ≠ 1`. Introduce `h`. Rewrite `hs1` using `[h, Complex.one_re]`. Conclude with `lt_irrefl _ hs1`.

Establish `hζ0 : riemannZeta s ≠ 0` using `riemannZeta_ne_zero_of_one_lt_re hs1`. Establish `hdist : ‖s - (3 / 2 + t * I)‖ ≤ 2 / 3`. Establish `h1 : s - (3 / 2 + t * I) = ((σ - 3 / 2 : ℝ) : ℂ)`. Rewrite using `[hsdef]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, Complex.norm_real, Real.norm_eq_abs, abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Take `⟨hfin, hbound⟩` from `hZ t s hdist hsne hζ0`. Use `set Z := {w : ℂ | ‖w - (3 / 2 + t * I)‖ ≤ 5 / 6 ∧ w ≠ 1 ∧ riemannZeta w = 0} with hZdef`.

Use `set S := ∑ᶠ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w) with hSdef`. Establish `hterm : ∀ w ∈ Z, 0 ≤ ((analyticOrderNatAt riemannZeta w : ℂ) / (s - w)).re`. Introduce `w hw`. Establish `hw1 : w.re ≤ 1`. Assume the negation of the conclusion as `h`.

Use `push Not at h`. Conclude with `riemannZeta_ne_zero_of_one_lt_re h hw.2.2`. Establish `hpos : 0 ≤ (s - w).re` using `by rw [Complex.sub_re, hsre]; linarith`. Rewrite using `[Complex.div_re]`. Simplify using `only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]`.

Conclude with `div_nonneg (mul_nonneg (Nat.cast_nonneg _) hpos) (Complex.normSq_nonneg _)`. Establish `hS : 0 ≤ S.re`. Rewrite using `[hSdef, finsum_mem_eq_finite_toFinset_sum _ hfin, Complex.re_sum]`. Conclude with `Finset.sum_nonneg fun w hw => hterm w (hfin.mem_toFinset.mp hw)`. Use `set E := deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - S with hEdef`.

Establish `hζ : deriv riemannZeta s / riemannZeta s = E - 1 / (s - 1) + S`. Rewrite using `[hEdef]`. Expand and normalize the polynomial expressions, which then agree. Establish `hE : -E.re ≤ C * Real.log (|t| + 2)` using `le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm E) hbound)`. Use `set D := deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s - deriv riemannZeta s / riemannZeta s with hDdef`.

Establish `hD : ‖D‖ ≤ Real.log q` using `norm_logDeriv_sub_le q hs1`. Establish `hDre : -D.re ≤ Real.log q` using `le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm D) hD)`. Establish `hLsplit : deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s = D + (E - 1 / (s - 1) + S)`. Rewrite using `[hDdef, ← hζ]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)`. Establish `hlq : 0 ≤ Real.log q` using `Real.log_nonneg hq1`. Establish `ht2 : (2 : ℝ) ≤ |t| + 2` using `by linarith [abs_nonneg t]`. Establish `hlt : 0 ≤ Real.log (|t| + 2)` using `Real.log_nonneg (by linarith)`. Establish `hlog : Real.log (q * (|t| + 2)) = Real.log q + Real.log (|t| + 2)` using `Real.log_mul (by linarith) (by linarith)`.

Rewrite using `[hLsplit, hlog]`. Simplify using `only [Complex.add_re, Complex.sub_re]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem neg_re_logDeriv_le : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 1 < σ → σ ≤ 2 → -(deriv (LFunction (1 : DirichletCharacter ℂ q)) (σ + t * I) / LFunction (1 : DirichletCharacter ℂ q) (σ + t * I)).re ≤ (1 / ((σ : ℂ) + t * I - 1)).re + C * Real.log (q * (|t| + 2)) := by
  obtain ⟨C, hC, hZ⟩ := GlobalTheory.T.logDeriv_riemannZeta_local_zero_sum
  refine ⟨C + 1, by linarith, ?_⟩
  intro q _ σ t hσ1 hσ2
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs1 : 1 < s.re := by rw [hsre]; exact hσ1
  have hsne : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs1
    exact lt_irrefl _ hs1
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have hdist : ‖s - (3 / 2 + t * I)‖ ≤ 2 / 3 := by
    have h1 : s - (3 / 2 + t * I) = ((σ - 3 / 2 : ℝ) : ℂ) := by
      rw [hsdef]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  obtain ⟨hfin, hbound⟩ := hZ t s hdist hsne hζ0
  set Z := {w : ℂ | ‖w - (3 / 2 + t * I)‖ ≤ 5 / 6 ∧ w ≠ 1 ∧ riemannZeta w = 0} with hZdef
  set S := ∑ᶠ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w) with hSdef
  have hterm : ∀ w ∈ Z, 0 ≤ ((analyticOrderNatAt riemannZeta w : ℂ) / (s - w)).re := by
    intro w hw
    have hw1 : w.re ≤ 1 := by
      by_contra h
      push Not at h
      exact riemannZeta_ne_zero_of_one_lt_re h hw.2.2
    have hpos : 0 ≤ (s - w).re := by rw [Complex.sub_re, hsre]; linarith
    rw [Complex.div_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hpos) (Complex.normSq_nonneg _)
  have hS : 0 ≤ S.re := by
    rw [hSdef, finsum_mem_eq_finite_toFinset_sum _ hfin, Complex.re_sum]
    exact Finset.sum_nonneg fun w hw => hterm w (hfin.mem_toFinset.mp hw)
  set E := deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - S with hEdef
  have hζ : deriv riemannZeta s / riemannZeta s = E - 1 / (s - 1) + S := by
    rw [hEdef]; ring
  have hE : -E.re ≤ C * Real.log (|t| + 2) :=
    le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm E) hbound)
  set D := deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s
    - deriv riemannZeta s / riemannZeta s with hDdef
  have hD : ‖D‖ ≤ Real.log q := norm_logDeriv_sub_le q hs1
  have hDre : -D.re ≤ Real.log q := le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm D) hD)
  have hLsplit : deriv (LFunction (1 : DirichletCharacter ℂ q)) s /
      LFunction (1 : DirichletCharacter ℂ q) s = D + (E - 1 / (s - 1) + S) := by
    rw [hDdef, ← hζ]; ring
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hlt : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith)
  have hlog : Real.log (q * (|t| + 2)) = Real.log q + Real.log (|t| + 2) :=
    Real.log_mul (by linarith) (by linarith)
  rw [hLsplit, hlog]
  simp only [Complex.add_re, Complex.sub_re]
  nlinarith

end GlobalTheory.PrincipalLogDeriv
