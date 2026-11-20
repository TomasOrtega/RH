import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl

noncomputable section

namespace GlobalTheory.ExpImage.TaylorEps

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage GlobalTheory.MemLoc
open Polynomial
open scoped Formalism.Per

section poly
variable (K : Type) [Field K] [CharZero K]

def logT (M : ℕ) : K[X] := ∑ k ∈ Finset.range M, C ((-1) ^ k * ((k + 1 : ℕ) : K)⁻¹) * X ^ (k + 1)

/- English proof (translation)
Proceed by induction on `M with`. Consider the case `zero => simp [logT]`. Consider the case `succ M ih`. Establish `h : ((M + 1 : ℕ) : K) ≠ 0` using `by exact_mod_cast M.succ_ne_zero`. Establish `e : derivative (C ((-1) ^ M * ((M + 1 : ℕ) : K)⁻¹) * X ^ (M + 1) : K[X]) = (-X) ^ M`.

Rewrite using `[derivative_C_mul, derivative_X_pow, ← mul_assoc, ← C_mul, mul_assoc, inv_mul_cancel₀ h, mul_one, neg_pow (X : K[X])]`. Simplify using the standard rewrite rules. Rewrite using `[logT, Finset.sum_range_succ, derivative_add, e, mul_add, ← logT, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logT_deriv (M : ℕ) : (1 + X) * derivative (logT K M) = 1 - (-X) ^ M := by
  induction M with
  | zero => simp [logT]
  | succ M ih =>
    have h : ((M + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast M.succ_ne_zero
    have e : derivative (C ((-1) ^ M * ((M + 1 : ℕ) : K)⁻¹) * X ^ (M + 1) : K[X]) = (-X) ^ M := by
      rw [derivative_C_mul, derivative_X_pow, ← mul_assoc, ← C_mul, mul_assoc, inv_mul_cancel₀ h,
        mul_one, neg_pow (X : K[X])]
      simp
    rw [logT, Finset.sum_range_succ, derivative_add, e, mul_add, ← logT, ih]
    ring

/- English proof (translation)
The claim follows from `Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (dvd_pow_self _ k.succ_ne_zero) _`.
-/
theorem X_dvd_logT (M : ℕ) : X ∣ logT K M :=
  Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (dvd_pow_self _ k.succ_ne_zero) _

/- English proof (translation)
Proceed by induction on `M with`. Consider the case `zero => simp`. Consider the case `succ M ih`. Establish `h : ((M + 1 : ℕ) : K) ≠ 0` using `by exact_mod_cast M.succ_ne_zero`. Establish `h' : ((M.factorial : ℕ) : K) ≠ 0` using `by exact_mod_cast M.factorial_ne_zero`.

Establish `e : (((M + 1).factorial : ℕ) : K)⁻¹ * ((M + 1 : ℕ) : K) = ((M.factorial : ℕ) : K)⁻¹`. Rewrite using `[Nat.factorial_succ, Nat.cast_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Finset.sum_range_succ, derivative_add, ih, Finset.sum_range_succ _ M, derivative_C_mul, derivative_pow, ← e, C_mul]`. Simplify using `only [Nat.add_sub_cancel]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem expT_deriv (L : K[X]) (M : ℕ) :
    derivative (∑ j ∈ Finset.range (M + 1), C ((j.factorial : K)⁻¹) * L ^ j) =
      derivative L * ∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * L ^ j := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h : ((M + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast M.succ_ne_zero
    have h' : ((M.factorial : ℕ) : K) ≠ 0 := by exact_mod_cast M.factorial_ne_zero
    have e : (((M + 1).factorial : ℕ) : K)⁻¹ * ((M + 1 : ℕ) : K) = ((M.factorial : ℕ) : K)⁻¹ := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      field_simp
    rw [Finset.sum_range_succ, derivative_add, ih, Finset.sum_range_succ _ M, derivative_C_mul,
      derivative_pow, ← e, C_mul]
    simp only [Nat.add_sub_cancel]
    ring

/- English proof (translation)
Break down `M with _ | M` into its components or cases. Simplify using the standard rewrite rules. Use `set L := logT K (M + 1) with hL`. Use `set D := 1 + X - ∑ j ∈ Finset.range (M + 1), C ((j.factorial : K)⁻¹) * L ^ j with hD`. Establish `h1 : X ^ M ∣ X * derivative D + derivative D - D`.

Establish `e : X * derivative D + derivative D - D = C ((M.factorial : K)⁻¹) * L ^ M + (-X) ^ (M + 1) * ∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * L ^ j`. Use `logT_deriv K (M + 1)` as an intermediate fact. Rewrite `this` using `[← hL]`. Rewrite using `[hD, derivative_sub, expT_deriv, Finset.sum_range_succ]`. Simplify using `only [derivative_add, derivative_one, derivative_X]`.

Take the linear combination `(-∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * L ^ j) * this`. Rewrite using `[e]`. Use `dvd_add (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (X_dvd_logT K _) M) _) (Dvd.dvd.mul_right ?_ _)` and prove the remaining obligations. Rewrite using `[neg_pow, pow_succ X]`. Conclude with `Dvd.dvd.mul_left (dvd_mul_right _ _) _`.

Establish `h0 : D.coeff 0 = 0`. Establish `hL0 : L.eval 0 = 0`. Rewrite using `[← coeff_zero_eq_eval_zero]`. Conclude with `X_dvd_iff.1 (X_dvd_logT K _)`. Rewrite using `[coeff_zero_eq_eval_zero, hD, Finset.sum_range_succ']`.

Simplify using `[eval_finset_sum, hL0]`. Rewrite `h1`, the goal using `[X_pow_dvd_iff]`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => exact fun _ => h0`.

Consider the case `succ d ih`. Introduce `hd`. Establish `a` using `ih (by omega)`. Establish `b` using `h1 d (by omega)`. Establish `c : (X * derivative D).coeff d = 0`.

Break down `d with _ | d` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[coeff_X_mul, coeff_derivative, a, zero_mul]`. Rewrite `b` using `[coeff_sub, coeff_add, c, a, coeff_derivative, zero_add, sub_zero]`. Conclude with `(mul_eq_zero.1 b).resolve_right (by exact_mod_cast d.succ_ne_zero)`.
-/
theorem exp_log_dvd (M : ℕ) :
    X ^ M ∣ 1 + X - ∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * logT K M ^ j := by
  rcases M with _ | M
  · simp
  set L := logT K (M + 1) with hL
  set D := 1 + X - ∑ j ∈ Finset.range (M + 1), C ((j.factorial : K)⁻¹) * L ^ j with hD
  have h1 : X ^ M ∣ X * derivative D + derivative D - D := by
    have e : X * derivative D + derivative D - D = C ((M.factorial : K)⁻¹) * L ^ M +
        (-X) ^ (M + 1) * ∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * L ^ j := by
      have := logT_deriv K (M + 1)
      rw [← hL] at this
      rw [hD, derivative_sub, expT_deriv, Finset.sum_range_succ]
      simp only [derivative_add, derivative_one, derivative_X]
      linear_combination (-∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * L ^ j) * this
    rw [e]
    refine dvd_add (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (X_dvd_logT K _) M) _)
      (Dvd.dvd.mul_right ?_ _)
    rw [neg_pow, pow_succ X]
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  have h0 : D.coeff 0 = 0 := by
    have hL0 : L.eval 0 = 0 := by
      rw [← coeff_zero_eq_eval_zero]; exact X_dvd_iff.1 (X_dvd_logT K _)
    rw [coeff_zero_eq_eval_zero, hD, Finset.sum_range_succ']
    simp [eval_finset_sum, hL0]
  rw [X_pow_dvd_iff] at h1 ⊢
  intro d
  induction d with
  | zero => exact fun _ => h0
  | succ d ih =>
    intro hd
    have a := ih (by omega)
    have b := h1 d (by omega)
    have c : (X * derivative D).coeff d = 0 := by
      rcases d with _ | d
      · simp
      · rw [coeff_X_mul, coeff_derivative, a, zero_mul]
    rw [coeff_sub, coeff_add, c, a, coeff_derivative, zero_add, sub_zero] at b
    exact (mul_eq_zero.1 b).resolve_right (by exact_mod_cast d.succ_ne_zero)

end poly

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

/- English proof (translation)
Proceed by induction on `f using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `add_mem hp hq`. Consider the case `monomial n a`. Rewrite using `[aeval_monomial]`.

Conclude with `qB_mul_mem a (by simpa using FilB_pow hx n)`.
-/
theorem aeval_mem {x : P.R.BdR} (hx : x ∈ FilB P 0) (f : ℚ_[l][X]) : aeval x f ∈ FilB P 0 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
    rw [aeval_monomial]
    exact qB_mul_mem a (by simpa using FilB_pow hx n)

/- English proof (translation)
The claim follows from `GlobalTheory.ThetaTie.eD_ιA T a`.
-/
theorem io_eq (T : LocTied l P AI) (a : Ainf l) :
    T.eD (io AI a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := GlobalTheory.ThetaTie.eD_ιA T a

/- English proof (translation)
Take `⟨y, hy, e⟩` from `T.t`. Establish `h : io AI (mu AI.ε) - tD P ∈ FilB P ((2 : ℕ) : ℤ)`. Use `(GlobalTheory.ThetaTie.fil_nat T 2 _).2 ⟨_, GlobalTheory.ThetaTie.log_mu (GlobalTheory.ThetaTie.isEps AI) hy, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_sub, e, io_eq]`. Use `add_mem (FilB_anti (a := 1) (by norm_num) h) (tD_mem (P := P))` as an intermediate fact.

Simplify using `using this`.
-/
theorem mu_mem (T : LocTied l P AI) : io AI (mu AI.ε) ∈ FilB P 1 := by
  obtain ⟨y, hy, e⟩ := T.t
  have h : io AI (mu AI.ε) - tD P ∈ FilB P ((2 : ℕ) : ℤ) := by
    refine (GlobalTheory.ThetaTie.fil_nat T 2 _).2 ⟨_, GlobalTheory.ThetaTie.log_mu (GlobalTheory.ThetaTie.isEps AI) hy, ?_⟩
    rw [map_sub, map_sub, e, io_eq]
  have := add_mem (FilB_anti (a := 1) (by norm_num) h) (tD_mem (P := P))
  simpa using this

/- English proof (translation)
Take `⟨y, hy, e⟩` from `T.t`. Establish `h : (M.factorial : P.R.BdR) * tD P - ∑ k ∈ Finset.range M, (-1) ^ k * ((M.factorial / (k + 1) : ℕ) : P.R.BdR) * io AI (mu AI.ε) ^ (k + 1) ∈ FilB P (M : ℤ)`. Use `(GlobalTheory.ThetaTie.fil_nat T M _).2 ⟨(M.factorial : Per.BdRp l) * y - algebraMap (Per.AinfP l) (Per.BdRp l) (∑ k ∈ Finset.range M, (-1) ^ k * ((M.factorial / (k + 1) : ℕ) : Per.AinfP l) * (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm AI.ε - 1)) ^ (k + 1)), ?_, ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l M _).2 ?_` and prove the remaining obligations. Rewrite using `[map_sub, GlobalTheory.ThetaTie.ev_alg, map_mul, map_natCast, GlobalTheory.CrisIncl.factorial_mul_ev l _ y (GlobalTheory.ThetaTie.isEps AI).1 hy M, sub_self]`.

Simplify using `only [map_sub, map_mul, map_natCast, map_sum, map_pow, map_neg, e, io_eq]`. Simplify using `only [map_one]`. Simplify using `only [aDp, mu, RingHom.comp_apply, map_sub, map_one]`. Establish `h0 : ((M.factorial : ℕ) : ℚ_[l]) ≠ 0` using `by exact_mod_cast M.factorial_ne_zero`. Use `qB_mul_mem ((M.factorial : ℕ) : ℚ_[l])⁻¹ h` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[mul_sub, ← mul_assoc, ← map_natCast (qB P), ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul, logT, map_sum, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hk' : k + 1 ∣ M.factorial` using `Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk)`.

Establish `h1 : ((k + 1 : ℕ) : ℚ_[l]) ≠ 0` using `by exact_mod_cast k.succ_ne_zero`. Establish `e1 : ((k + 1 : ℕ) : ℚ_[l])⁻¹ = ((M.factorial : ℕ) : ℚ_[l])⁻¹ * ((M.factorial / (k + 1) : ℕ) : ℚ_[l])`. Rewrite using `[Nat.cast_div hk' h1]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[map_mul, aeval_C, map_pow, aeval_X, e1]`.

Simplify using `only [map_mul, map_pow, map_neg, map_one, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem t_sub_log (T : LocTied l P AI) (M : ℕ) :
    tD P - aeval (io AI (mu AI.ε)) (logT ℚ_[l] M) ∈ FilB P (M : ℤ) := by
  obtain ⟨y, hy, e⟩ := T.t
  have h : (M.factorial : P.R.BdR) * tD P - ∑ k ∈ Finset.range M,
      (-1) ^ k * ((M.factorial / (k + 1) : ℕ) : P.R.BdR) * io AI (mu AI.ε) ^ (k + 1) ∈
        FilB P (M : ℤ) := by
    refine (GlobalTheory.ThetaTie.fil_nat T M _).2 ⟨(M.factorial : Per.BdRp l) * y -
      algebraMap (Per.AinfP l) (Per.BdRp l) (∑ k ∈ Finset.range M,
        (-1) ^ k * ((M.factorial / (k + 1) : ℕ) : Per.AinfP l) *
          (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm AI.ε - 1)) ^ (k + 1)), ?_, ?_⟩
    · refine (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l M _).2 ?_
      rw [map_sub, GlobalTheory.ThetaTie.ev_alg, map_mul, map_natCast,
        GlobalTheory.CrisIncl.factorial_mul_ev l _ y (GlobalTheory.ThetaTie.isEps AI).1 hy M, sub_self]
    · simp only [map_sub, map_mul, map_natCast, map_sum, map_pow, map_neg, e, io_eq]
      simp only [map_one]
      simp only [aDp, mu, RingHom.comp_apply, map_sub, map_one]
  have h0 : ((M.factorial : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast M.factorial_ne_zero
  have := qB_mul_mem ((M.factorial : ℕ) : ℚ_[l])⁻¹ h
  convert this using 1
  rw [mul_sub, ← mul_assoc, ← map_natCast (qB P), ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul,
    logT, map_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k + 1 ∣ M.factorial := Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk)
  have h1 : ((k + 1 : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast k.succ_ne_zero
  have e1 : ((k + 1 : ℕ) : ℚ_[l])⁻¹ =
      ((M.factorial : ℕ) : ℚ_[l])⁻¹ * ((M.factorial / (k + 1) : ℕ) : ℚ_[l]) := by
    rw [Nat.cast_div hk' h1]
    field_simp
  rw [map_mul, aeval_C, map_pow, aeval_X, e1]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

/- English proof (translation)
Establish `hm` using `mu_mem T`. Establish `hm0` using `FilB_anti (a := 0) (by norm_num) hm`. Establish `hL` using `aeval_mem hm0 (logT ℚ_[l] M)`. Establish `ht` using `FilB_anti (a := 0) (by norm_num) (tD_mem (P := P))`. Establish `hd` using `t_sub_log T M`.

Take `⟨Q, hQ⟩` from `exp_log_dvd ℚ_[l] M`. Establish `h1` using `congrArg (aeval (io AI (mu AI.ε))) hQ`. Simplify using `only [map_sub, map_add, map_one, aeval_X, map_sum, map_mul, aeval_C, map_pow] at h1`. Establish `h2` using `FilB_zero_mul (aeval_mem hm0 Q) (FilB_pow hm M)`. Rewrite `h2` using `[mul_one, mul_comm, ← h1]`.

Generalize the expression as in `aeval (io AI (mu AI.ε)) (logT ℚ_[l] M) = L at hL hd h2`. Establish `h3 : ∀ j : ℕ, tD P ^ j - L ^ j ∈ FilB P (M : ℤ)`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`.

Consider the case `succ j ih`. Use `add_mem (FilB_zero_mul ht ih) (FilB_zero_mul (x := L ^ j) (by simpa using FilB_pow hL j) hd)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Establish `h4` using `Submodule.sum_mem (FilB P (M : ℤ)) (t := Finset.range M) fun j _ => qB_mul_mem ((j.factorial : ℚ_[l])⁻¹) (h3 j)`.

Establish `e : io AI (WittVector.teichmuller l AI.ε) = 1 + io AI (mu AI.ε)`. Rewrite using `[mu, map_sub, map_one, add_sub_cancel]`. Use `sub_mem h2 h4` as an intermediate fact. Rewrite using `[e]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [mul_sub, Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eps_sub_exp (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (M : ℕ) : io AI (WittVector.teichmuller l AI.ε) -
      ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * tD P ^ j ∈ FilB P (M : ℤ) := by
  have hm := mu_mem T
  have hm0 := FilB_anti (a := 0) (by norm_num) hm
  have hL := aeval_mem hm0 (logT ℚ_[l] M)
  have ht := FilB_anti (a := 0) (by norm_num) (tD_mem (P := P))
  have hd := t_sub_log T M
  obtain ⟨Q, hQ⟩ := exp_log_dvd ℚ_[l] M
  have h1 := congrArg (aeval (io AI (mu AI.ε))) hQ
  simp only [map_sub, map_add, map_one, aeval_X, map_sum, map_mul, aeval_C, map_pow] at h1
  have h2 := FilB_zero_mul (aeval_mem hm0 Q) (FilB_pow hm M)
  rw [mul_one, mul_comm, ← h1] at h2
  generalize aeval (io AI (mu AI.ε)) (logT ℚ_[l] M) = L at hL hd h2
  have h3 : ∀ j : ℕ, tD P ^ j - L ^ j ∈ FilB P (M : ℤ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := add_mem (FilB_zero_mul ht ih)
        (FilB_zero_mul (x := L ^ j) (by simpa using FilB_pow hL j) hd)
      convert this using 1
      ring
  have h4 := Submodule.sum_mem (FilB P (M : ℤ)) (t := Finset.range M)
    fun j _ => qB_mul_mem ((j.factorial : ℚ_[l])⁻¹) (h3 j)
  have e : io AI (WittVector.teichmuller l AI.ε) = 1 + io AI (mu AI.ε) := by
    rw [mu, map_sub, map_one, add_sub_cancel]
  have := sub_mem h2 h4
  rw [e]
  convert this using 1
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end GlobalTheory.ExpImage.TaylorEps
