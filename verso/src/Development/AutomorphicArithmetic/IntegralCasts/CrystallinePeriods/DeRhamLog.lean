import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow

noncomputable section

open Ideal Polynomial

namespace Reformulated.AutPerF

universe u v

section Trunc

variable {B : Type*} [CommRing B] [Algebra ℚ B]

/- English proof (translation)
Simplify using `[truncLog]`.
-/
theorem truncLog_zero (N : ℕ) : truncLog N (0 : B) = 0 := by simp [truncLog]

/- English proof (translation)
Establish `h1 : derivative (truncLog N z) = derivative z * ∑ k ∈ Finset.range N, (-z) ^ k`. Rewrite using `[truncLog, derivative_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[derivative_smul, derivative_pow_succ, neg_pow z]`. Establish `e : (C ((k : B) + 1) : B[X]) = algebraMap ℚ B[X] (k + 1)` using `by simp`.

Establish `e2 : ((-1 : B[X])) ^ k = algebraMap ℚ B[X] ((-1) ^ k)` using `by simp`. Rewrite using `[e, e2, Algebra.smul_def, ← mul_assoc, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ (by positivity)]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `geom_sum_mul_neg (-z) N`. Rewrite `h2` using `[neg_pow z N, hz, mul_zero, sub_zero, sub_neg_eq_add]`.

Rewrite using `[h1, mul_assoc, h2, mul_one]`.
-/
theorem derivative_truncLog_mul (N : ℕ) (z : B[X]) (hz : z ^ N = 0) :
    derivative (truncLog N z) * (1 + z) = derivative z := by
  have h1 : derivative (truncLog N z) = derivative z * ∑ k ∈ Finset.range N, (-z) ^ k := by
    rw [truncLog, derivative_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [derivative_smul, derivative_pow_succ, neg_pow z]
    have e : (C ((k : B) + 1) : B[X]) = algebraMap ℚ B[X] (k + 1) := by simp
    have e2 : ((-1 : B[X])) ^ k = algebraMap ℚ B[X] ((-1) ^ k) := by simp
    rw [e, e2, Algebra.smul_def, ← mul_assoc, ← mul_assoc, ← map_mul,
      div_mul_cancel₀ _ (by positivity)]
    ring
  have h2 := geom_sum_mul_neg (-z) N
  rw [neg_pow z N, hz, mul_zero, sub_zero, sub_neg_eq_add] at h2
  rw [h1, mul_assoc, h2, mul_one]

/- English proof (translation)
Establish `hX : IsNilpotent (C x * X : B[X])` using `⟨n, by rw [mul_pow, ← C_pow, hx, C_0, zero_mul]⟩`. Establish `hY : IsNilpotent (C y : B[X])` using `⟨n, by rw [← C_pow, hy, C_0]⟩`. Take `⟨M, hM⟩ : IsNilpotent (C x * X + C y + C x * X * C y : B[X])` from `(Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_add hX hY) ((Commute.all _ _).isNilpotent_mul_left hY)`. Use `set N := max M n`. Establish `hM'` using `pow_eq_zero_of_le (le_max_left M n) hM`.

Establish `hX' : (C x * X : B[X]) ^ N = 0`. Rewrite using `[mul_pow, ← C_pow, pow_eq_zero_of_le (le_max_right M n) hx, C_0, zero_mul]`. Establish `d1` using `derivative_truncLog_mul N _ hM'`. Establish `d2` using `derivative_truncLog_mul N _ hX'`. Establish `hu : IsUnit (1 + (C x * X + C y + C x * X * C y) : B[X])` using `IsNilpotent.isUnit_one_add ⟨M, hM⟩`.

Establish `hD : derivative (truncLog N (C x * X + C y + C x * X * C y) - truncLog N (C x * X)) = 0`. Use `hu.mul_right_cancel ?_` and prove the remaining obligations. Rewrite using `[derivative_sub, sub_mul, d1, zero_mul, show (1 + (C x * X + C y + C x * X * C y) : B[X]) = (1 + C x * X) * (1 + C y) by ring, ← mul_assoc, d2]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Use `haveI : IsAddTorsionFree B := IsAddTorsionFree.of_module_rat B`. Establish `hC` using `eq_C_of_derivative_eq_zero hD`. Establish `e1` using `congrArg (evalRingHom 1) hC`. Establish `e0` using `congrArg (evalRingHom 0) hC`. Rewrite `e0`, `e1` using `[map_sub, map_truncLog, map_truncLog]`.

Simplify using `only [coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X, mul_one, mul_zero, zero_add, zero_mul, add_zero, truncLog_zero, sub_zero] at e0 e1`. Rewrite using `[← truncLog_eq_of_pow_eq_zero hx (le_max_right M n), ← truncLog_eq_of_pow_eq_zero hy (le_max_right M n), ← truncLog_eq_of_pow_eq_zero hxy (le_max_right M n), e0, ← e1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem truncLog_add {n : ℕ} {x y : B} (hx : x ^ n = 0) (hy : y ^ n = 0)
    (hxy : (x + y + x * y) ^ n = 0) :
    truncLog n (x + y + x * y) = truncLog n x + truncLog n y := by
  have hX : IsNilpotent (C x * X : B[X]) := ⟨n, by rw [mul_pow, ← C_pow, hx, C_0, zero_mul]⟩
  have hY : IsNilpotent (C y : B[X]) := ⟨n, by rw [← C_pow, hy, C_0]⟩
  obtain ⟨M, hM⟩ : IsNilpotent (C x * X + C y + C x * X * C y : B[X]) :=
    (Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_add hX hY)
      ((Commute.all _ _).isNilpotent_mul_left hY)
  set N := max M n
  have hM' := pow_eq_zero_of_le (le_max_left M n) hM
  have hX' : (C x * X : B[X]) ^ N = 0 := by
    rw [mul_pow, ← C_pow, pow_eq_zero_of_le (le_max_right M n) hx, C_0, zero_mul]
  have d1 := derivative_truncLog_mul N _ hM'
  have d2 := derivative_truncLog_mul N _ hX'
  have hu : IsUnit (1 + (C x * X + C y + C x * X * C y) : B[X]) :=
    IsNilpotent.isUnit_one_add ⟨M, hM⟩
  have hD : derivative (truncLog N (C x * X + C y + C x * X * C y) - truncLog N (C x * X)) = 0 := by
    refine hu.mul_right_cancel ?_
    rw [derivative_sub, sub_mul, d1, zero_mul,
      show (1 + (C x * X + C y + C x * X * C y) : B[X]) = (1 + C x * X) * (1 + C y) by ring,
      ← mul_assoc, d2]
    simp
    ring
  haveI : IsAddTorsionFree B := IsAddTorsionFree.of_module_rat B
  have hC := eq_C_of_derivative_eq_zero hD
  have e1 := congrArg (evalRingHom 1) hC
  have e0 := congrArg (evalRingHom 0) hC
  rw [map_sub, map_truncLog, map_truncLog] at e0 e1
  simp only [coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X, mul_one, mul_zero, zero_add,
    zero_mul, add_zero, truncLog_zero, sub_zero] at e0 e1
  rw [← truncLog_eq_of_pow_eq_zero hx (le_max_right M n),
    ← truncLog_eq_of_pow_eq_zero hy (le_max_right M n),
    ← truncLog_eq_of_pow_eq_zero hxy (le_max_right M n), e0, ← e1]
  ring

end Trunc

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]

namespace BdRPlus

/- English proof (translation)
The claim follows from `evalₐ_pow_eq_zero _ ((theta_eq_zero_iff x).1 hx) n`.
-/
theorem eval_pow_eq_zero {x : BdRPlus p R} (hx : theta p R x = 0) (n : ℕ) :
    eval p R n x ^ n = 0 := evalₐ_pow_eq_zero _ ((theta_eq_zero_iff x).1 hx) n

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem log_congr {u v : BdRPlus p R} (h : u = v) (hu : theta p R u = 1) (hv : theta p R v = 1) :
    log u hu = log v hv := by subst h; rfl

/- English proof (translation)
Use `ext_eval fun n => ?_` and prove the remaining obligations. Establish `e : eval p R n (u * v - 1) = eval p R n (u - 1) + eval p R n (v - 1) + eval p R n (u - 1) * eval p R n (v - 1)`. Rewrite using `[← map_mul, ← map_add, ← map_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[map_add, eval_log, eval_log, eval_log, e]`. Use `truncLog_add (eval_pow_eq_zero (by simp [hu]) n) (eval_pow_eq_zero (by simp [hv]) n) ?_` and prove the remaining obligations. Rewrite using `[← e]`. Conclude with `eval_pow_eq_zero (by simp [hu, hv]) n`.
-/
theorem log_mul (u v : BdRPlus p R) (hu : theta p R u = 1) (hv : theta p R v = 1) :
    log (u * v) (by rw [map_mul, hu, hv, one_mul]) = log u hu + log v hv := by
  refine ext_eval fun n => ?_
  have e : eval p R n (u * v - 1) =
      eval p R n (u - 1) + eval p R n (v - 1) + eval p R n (u - 1) * eval p R n (v - 1) := by
    rw [← map_mul, ← map_add, ← map_add]; congr 1; ring
  rw [map_add, eval_log, eval_log, eval_log, e]
  refine truncLog_add (eval_pow_eq_zero (by simp [hu]) n) (eval_pow_eq_zero (by simp [hv]) n) ?_
  rw [← e]
  exact eval_pow_eq_zero (by simp [hu, hv]) n

/- English proof (translation)
The claim follows from `ext_eval fun n => by rw [eval_log, sub_self, map_zero, truncLog_zero]`.
-/
theorem log_one : log (1 : BdRPlus p R) (map_one _) = 0 :=
  ext_eval fun n => by rw [eval_log, sub_self, map_zero, truncLog_zero]

/- English proof (translation)
Rewrite using `[eval_log, truncLog, Finset.sum_range_succ, Finset.sum_range_one, eval_pow_eq_zero (x := u - 1) (by simp [hu]) 2]`. Simplify using the standard rewrite rules.
-/
theorem eval_two_log (u : BdRPlus p R) (hu : theta p R u = 1) :
    eval p R 2 (log u hu) = eval p R 2 (u - 1) := by
  rw [eval_log, truncLog, Finset.sum_range_succ, Finset.sum_range_one,
    eval_pow_eq_zero (x := u - 1) (by simp [hu]) 2]
  simp

/- English proof (translation)
Rewrite using `[theta_eq_of_eval_one (a := 0), map_zero]`. Rewrite using `[eval_log, truncLog, Finset.sum_range_one, zero_add, eval_pow_eq_zero (x := u - 1) (by simp [hu]) 1]`. Simplify using the standard rewrite rules.
-/
theorem theta_log (u : BdRPlus p R) (hu : theta p R u = 1) : theta p R (log u hu) = 0 := by
  rw [theta_eq_of_eval_one (a := 0), map_zero]
  rw [eval_log, truncLog, Finset.sum_range_one, zero_add,
    eval_pow_eq_zero (x := u - 1) (by simp [hu]) 1]
  simp

def logTeich (η : tateModule p R) : BdRPlus p R :=
  log (algebraMap (Ainf p R) _ (Ainf.teich p η.1)) (by
    rw [IsScalarTower.algebraMap_apply _ (AinfInv p R), theta_algebraMap, AinfInv.theta_algebraMap,
      Ainf.theta_teich, show PreTilt.untilt η.1 = 1 from η.2, map_one])

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[p] (BdRPlus p R)), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero), map_one]`.
-/
theorem p_mul_inv : (p : BdRPlus p R) * algebraMap ℚ_[p] _ (p : ℚ_[p])⁻¹ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] (BdRPlus p R)), ← map_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero), map_one]

def teichDivP (ϖ : PFlat p R) : BdRPlus p R :=
  algebraMap (Ainf p R) _ (Ainf.teich p ϖ.1) * algebraMap ℚ_[p] _ (p : ℚ_[p])⁻¹

/- English proof (translation)
Rewrite using `[teichDivP, map_mul, IsScalarTower.algebraMap_apply _ (AinfInv p R), theta_algebraMap, AinfInv.theta_algebraMap, Ainf.theta_teich, ϖ.2, map_natCast, ← map_natCast (theta p R), ← map_mul, p_mul_inv, map_one]`.
-/
theorem theta_teichDivP (ϖ : PFlat p R) : theta p R (teichDivP ϖ) = 1 := by
  rw [teichDivP, map_mul, IsScalarTower.algebraMap_apply _ (AinfInv p R), theta_algebraMap,
    AinfInv.theta_algebraMap, Ainf.theta_teich, ϖ.2, map_natCast, ← map_natCast (theta p R),
    ← map_mul, p_mul_inv, map_one]

def logFlat (ϖ : PFlat p R) : BdRPlus p R := log (teichDivP ϖ) (theta_teichDivP ϖ)

/- English proof (translation)
Rewrite using `[logFlat, logFlat, logTeich, ← log_mul]`. Conclude with `log_congr (by simp [teichDivP, PFlat.twist, mul_assoc]) _ _`.
-/
theorem logFlat_twist (η : tateModule p R) (ϖ : PFlat p R) :
    logFlat (ϖ.twist η) = logTeich η + logFlat ϖ := by
  rw [logFlat, logFlat, logTeich, ← log_mul]
  exact log_congr (by simp [teichDivP, PFlat.twist, mul_assoc]) _ _

/- English proof (translation)
Rewrite using `[logTeich, map_log]`. Conclude with `log_congr (by simp) _ _`.
-/
theorem map_logTeich (f : R →+* S) (η : tateModule p R) :
    map p f (logTeich η) = logTeich (tateModule.map p f η) := by
  rw [logTeich, map_log]
  exact log_congr (by simp) _ _

/- English proof (translation)
Rewrite using `[logFlat, map_log]`. Conclude with `log_congr (by simp [teichDivP]) _ _`.
-/
theorem map_logFlat (f : R →+* S) (ϖ : PFlat p R) :
    map p f (logFlat ϖ) = logFlat (PFlat.map p f ϖ) := by
  rw [logFlat, map_log]
  exact log_congr (by simp [teichDivP]) _ _

end BdRPlus

end Reformulated.AutPerF
