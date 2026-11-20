import Mathlib
import GroundTheory.PAdicHodge.ACrisLog
import GroundTheory.PAdicHodge.LogPowSeries
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector Polynomial

namespace ACris

section Coefficients

variable (q : ℕ)

def powCoeff (N m : ℕ) : ℤ := ((((1 : ℤ[X]) + X) ^ q - 1) ^ N).coeff m

/- English proof (translation)
Use `(natDegree_pow_le).trans ?_` and prove the remaining obligations. Rewrite using `[mul_comm q N]`. Use `Nat.mul_le_mul_left N ?_` and prove the remaining obligations. Use `(natDegree_sub_le _ _).trans (max_le ?_ (by simp))` and prove the remaining obligations. Use `(natDegree_pow_le).trans ?_` and prove the remaining obligations.

Establish `: ((1 : ℤ[X]) + X).natDegree ≤ 1` using `(natDegree_add_le _ _).trans (by simp)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem natDegree_one_add_X_pow_sub_one_pow_le (N : ℕ) :
    ((((1 : ℤ[X]) + X) ^ q - 1) ^ N).natDegree ≤ q * N := by
  refine (natDegree_pow_le).trans ?_
  rw [mul_comm q N]
  refine Nat.mul_le_mul_left N ?_
  refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
  refine (natDegree_pow_le).trans ?_
  have : ((1 : ℤ[X]) + X).natDegree ≤ 1 := (natDegree_add_le _ _).trans (by simp)
  nlinarith

/- English proof (translation)
The claim follows from `coeff_one_add_X_pow_sub_one_pow_of_lt q h`.
-/
theorem powCoeff_of_lt {N m : ℕ} (h : m < N) : powCoeff q N m = 0 :=
  coeff_one_add_X_pow_sub_one_pow_of_lt q h

/- English proof (translation)
The claim follows from `coeff_eq_zero_of_natDegree_lt ((natDegree_one_add_X_pow_sub_one_pow_le q N).trans_lt h)`.
-/
theorem powCoeff_of_gt {N m : ℕ} (h : q * N < m) : powCoeff q N m = 0 :=
  coeff_eq_zero_of_natDegree_lt ((natDegree_one_add_X_pow_sub_one_pow_le q N).trans_lt h)

/- English proof (translation)
Establish `h` using `log_pow_coeff_int q (j + 1) (Nat.succ_pos j)`. Establish `hI : Finset.Icc 1 (j + 1) = Finset.Ico 1 (j + 2)` using `by ext; simp; omega`. Rewrite `h` using `[hI, Finset.sum_Ico_eq_sum_range]`. Simplify using `only [Nat.add_sub_cancel, show j + 2 - 1 = j + 1 by omega] at h`. Rewrite using `[← h]`.

Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[add_comm 1 n, Nat.add_sub_cancel, powCoeff]`.
-/
theorem sum_powCoeff (j : ℕ) :
    ∑ n ∈ Finset.range (j + 1), (-1 : ℤ) ^ n * powCoeff q (n + 1) (j + 1) *
      (((j + 1).factorial / (n + 1) : ℕ) : ℤ) = (-1) ^ j * q * j.factorial := by
  have h := log_pow_coeff_int q (j + 1) (Nat.succ_pos j)
  have hI : Finset.Icc 1 (j + 1) = Finset.Ico 1 (j + 2) := by ext; simp; omega
  rw [hI, Finset.sum_Ico_eq_sum_range] at h
  simp only [Nat.add_sub_cancel, show j + 2 - 1 = j + 1 by omega] at h
  rw [← h]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [add_comm 1 n, Nat.add_sub_cancel, powCoeff]

/- English proof (translation)
Take `⟨c, hc⟩` from `Nat.factorial_dvd_factorial (Nat.succ_le_succ h)`. Rewrite using `[hc, Nat.factorial_succ, mul_assoc, Nat.mul_div_cancel_left _ n.succ_pos, ← mul_assoc, Nat.mul_div_cancel_left _ (Nat.mul_pos n.succ_pos n.factorial_pos)]`.
-/
theorem factorial_div_succ_eq {n j : ℕ} (h : n ≤ j) :
    (j + 1).factorial / (n + 1) = n.factorial * ((j + 1).factorial / (n + 1).factorial) := by
  obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial (Nat.succ_le_succ h)
  rw [hc, Nat.factorial_succ, mul_assoc, Nat.mul_div_cancel_left _ n.succ_pos,
    ← mul_assoc, Nat.mul_div_cancel_left _ (Nat.mul_pos n.succ_pos n.factorial_pos)]

end Coefficients

end ACris

namespace ACris

section Expansion

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)

variable (p) in

def logCoeff (n j : ℕ) : ℤ :=
  (-1) ^ n * powCoeff p (n + 1) (j + 1) * (((j + 1).factorial / (n + 1) : ℕ) : ℤ)

omit hp in
/- English proof (translation)
Simplify using `[logCoeff, powCoeff_of_lt p (show j + 1 < n + 1 by omega)]`.
-/
theorem logCoeff_of_lt {n j : ℕ} (h : j < n) : logCoeff p n j = 0 := by
  simp [logCoeff, powCoeff_of_lt p (show j + 1 < n + 1 by omega)]

omit hp in
/- English proof (translation)
Simplify using `[logCoeff, powCoeff_of_gt p h]`.
-/
theorem logCoeff_of_gt {n j : ℕ} (h : p * (n + 1) < j + 1) : logCoeff p n j = 0 := by
  simp [logCoeff, powCoeff_of_gt p h]

omit hp in
/- English proof (translation)
Distinguish the cases in `h : n ≤ j`. Rewrite using `[logCoeff, factorial_div_succ_eq h, Nat.cast_mul]`. Conclude with `Dvd.dvd.mul_left (Dvd.intro _ rfl) _`. Rewrite using `[logCoeff_of_lt (by omega)]`. Conclude with `dvd_zero _`.
-/
theorem factorial_dvd_logCoeff (n j : ℕ) : (n.factorial : ℤ) ∣ logCoeff p n j := by
  by_cases h : n ≤ j
  · rw [logCoeff, factorial_div_succ_eq h, Nat.cast_mul]
    exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _
  · rw [logCoeff_of_lt (by omega)]
    exact dvd_zero _

omit hp in
/- English proof (translation)
The claim follows from `sum_powCoeff p j`.
-/
theorem sum_logCoeff (j : ℕ) :
    ∑ n ∈ Finset.range (j + 1), logCoeff p n j = (-1) ^ j * p * j.factorial :=
  sum_powCoeff p j

/- English proof (translation)
Establish `hdeg : ((((1 : ℤ[X]) + X) ^ p - 1) ^ N).natDegree < L + 1` using `Nat.lt_succ_of_le ((natDegree_one_add_X_pow_sub_one_pow_le p N).trans hL)`. Establish `h` using `aeval_eq_sum_range' (R := ℤ) hdeg x`. Simplify using `only [map_pow, map_sub, map_add, map_one, aeval_X] at h`. Rewrite using `[h]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[zsmul_eq_mul, powCoeff]`.
-/
theorem one_add_pow_sub_one_pow_eq_sum (x : AInf K p) (N L : ℕ) (hL : p * N ≤ L) :
    ((1 + x) ^ p - 1) ^ N =
      ∑ m ∈ Finset.range (L + 1), (powCoeff p N m : AInf K p) * x ^ m := by
  have hdeg : ((((1 : ℤ[X]) + X) ^ p - 1) ^ N).natDegree < L + 1 :=
    Nat.lt_succ_of_le ((natDegree_one_add_X_pow_sub_one_pow_le p N).trans hL)
  have h := aeval_eq_sum_range' (R := ℤ) hdeg x
  simp only [map_pow, map_sub, map_add, map_one, aeval_X] at h
  rw [h]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [zsmul_eq_mul, powCoeff]

/- English proof (translation)
Establish `h1` using `isUnit_natCast (K := K) (p := p) (Nat.succ_ne_zero n)`. Apply `h1.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[← mul_assoc, ← Nat.cast_mul, ← Nat.factorial_succ, factorial_mul_dpow, ← map_pow, one_add_pow_sub_one_pow_eq_sum x (n + 1) L hL, map_sum, Finset.sum_range_succ', Finset.mul_sum]`. Simplify using `only [map_mul, map_intCast, map_pow, pow_zero, mul_one, powCoeff_of_lt p n.succ_pos, Int.cast_zero, zero_mul, map_zero, add_zero]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Distinguish the cases in `h : n ≤ j`. Establish `hdvd : n + 1 ∣ (j + 1).factorial` using `Nat.dvd_factorial n.succ_pos (Nat.succ_le_succ h)`. Rewrite using `[← factorial_mul_dpow (j + 1) x]`. Take `⟨d, hd⟩ : ∃ d, (j + 1).factorial / (n + 1) = d` from `⟨_, rfl⟩`. Establish `hd' : (n + 1) * d = (j + 1).factorial` using `by rw [← hd, Nat.mul_div_cancel' hdvd]`.

Rewrite using `[hd, ← hd']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[powCoeff_of_lt p (show j + 1 < n + 1 by omega)]`. Simplify using the standard rewrite rules.
-/
theorem factorial_mul_dpow_eq_sum (x : AInf K p) (n L : ℕ) (hL : p * (n + 1) ≤ L) :
    (n.factorial : 𝔸) * dpow (n + 1) ((1 + x) ^ p - 1) =
      ∑ j ∈ Finset.range L, ((powCoeff p (n + 1) (j + 1) *
        (((j + 1).factorial / (n + 1) : ℕ) : ℤ) : ℤ) : 𝔸) * dpow (j + 1) x := by
  have h1 := isUnit_natCast (K := K) (p := p) (Nat.succ_ne_zero n)
  apply h1.mul_left_cancel
  rw [← mul_assoc, ← Nat.cast_mul, ← Nat.factorial_succ, factorial_mul_dpow, ← map_pow,
    one_add_pow_sub_one_pow_eq_sum x (n + 1) L hL, map_sum, Finset.sum_range_succ', Finset.mul_sum]
  simp only [map_mul, map_intCast, map_pow, pow_zero, mul_one, powCoeff_of_lt p n.succ_pos,
    Int.cast_zero, zero_mul, map_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : n ≤ j
  · have hdvd : n + 1 ∣ (j + 1).factorial := Nat.dvd_factorial n.succ_pos (Nat.succ_le_succ h)
    rw [← factorial_mul_dpow (j + 1) x]
    obtain ⟨d, hd⟩ : ∃ d, (j + 1).factorial / (n + 1) = d := ⟨_, rfl⟩
    have hd' : (n + 1) * d = (j + 1).factorial := by rw [← hd, Nat.mul_div_cancel' hdvd]
    rw [hd, ← hd']
    push_cast
    ring
  · rw [powCoeff_of_lt p (show j + 1 < n + 1 by omega)]
    simp

variable {x : AInf K p}

/- English proof (translation)
Rewrite `hx`, the goal using `[RingHom.mem_ker]`. Rewrite using `[map_sub, map_pow, map_add, map_one, hx, add_zero, one_pow, sub_self]`.
-/
theorem one_add_pow_sub_one_mem (hx : x ∈ RingHom.ker θ) : (1 + x) ^ p - 1 ∈ RingHom.ker θ := by
  rw [RingHom.mem_ker] at hx ⊢
  rw [map_sub, map_pow, map_add, map_one, hx, add_zero, one_pow, sub_self]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [logTermZero, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg, Subalgebra.coe_one, SubringClass.coe_natCast, coe_dpowZero, AddSubmonoidClass.coe_finsetSum, SubringClass.coe_intCast]`. Rewrite using `[mul_assoc, factorial_mul_dpow_eq_sum x n L hL, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [logCoeff]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logTermZero_one_add_pow (hx : x ∈ RingHom.ker θ) (n L : ℕ) (hL : p * (n + 1) ≤ L) :
    logTermZero (one_add_pow_sub_one_mem hx) n =
      ∑ j ∈ Finset.range L, (logCoeff p n j : ACrisZero K p) * dpowZero hx (j + 1) := by
  apply Subtype.ext
  simp only [logTermZero, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg,
    Subalgebra.coe_one, SubringClass.coe_natCast, coe_dpowZero, AddSubmonoidClass.coe_finsetSum,
    SubringClass.coe_intCast]
  rw [mul_assoc, factorial_mul_dpow_eq_sum x n L hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [logCoeff]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[← Finset.sum_mul, ← Int.cast_sum, sum_logCoeff, logTermZero]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem p_mul_logTermZero (hx : x ∈ RingHom.ker θ) (j : ℕ) :
    (p : ACrisZero K p) * logTermZero hx j =
      ∑ n ∈ Finset.range (j + 1), (logCoeff p n j : ACrisZero K p) * dpowZero hx (j + 1) := by
  rw [← Finset.sum_mul, ← Int.cast_sum, sum_logCoeff, logTermZero]
  push_cast
  ring

end Expansion

end ACris

namespace ACris

section PhiT

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
local notation "𝔭₀" => Ideal.span {(p : ACrisZero K p)}

variable {x : AInf K p}

/- English proof (translation)
Establish `hpM : M ≤ p * M` using `Nat.le_mul_of_pos_left M hp.out.pos`. Rewrite using `[Finset.sum_congr rfl fun n hn => logTermZero_one_add_pow hx n (p * M) (Nat.mul_le_mul_left p (Finset.mem_range.1 hn)), Finset.sum_congr rfl fun j _ => p_mul_logTermZero hx j]`. Establish `h1 : ∀ j ∈ Finset.range M, ∑ n ∈ Finset.range (j + 1), (logCoeff p n j : ACrisZero K p) * dpowZero hx (j + 1) = ∑ n ∈ Finset.range M, (logCoeff p n j : ACrisZero K p) * dpowZero hx (j + 1)`. Introduce `j hj`. Apply `Finset.sum_subset (Finset.range_subset_range.2 (Finset.mem_range.1 hj))` to reduce the goal to its premises.

Introduce `n _ hn`. Rewrite `hn` using `[Finset.mem_range, not_lt]`. Rewrite using `[logCoeff_of_lt (by omega), Int.cast_zero, zero_mul]`. Rewrite using `[Finset.sum_congr rfl h1, Finset.sum_comm (s := Finset.range M) (t := Finset.range (p * M)), ← Finset.sum_range_add_sum_Ico _ hpM, sub_add_cancel_left]`. Use `neg_mem (Ideal.sum_mem _ fun j hj => Ideal.sum_mem _ fun n _ => ?_)` and prove the remaining obligations.

Establish `hj` using `(Finset.mem_Ico.1 hj).1`. Distinguish the cases in `hc : p * (n + 1) < j + 1`. Rewrite using `[logCoeff_of_gt hc, Int.cast_zero, zero_mul]`. Conclude with `zero_mem _`. Establish `hn : p * k ≤ n`.

Assume the negation of the conclusion as `hlt`. Establish `: p * (n + 1) ≤ p * (p * k)` using `Nat.mul_le_mul_left p (by omega)`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨z, hz⟩` from `factorial_dvd_logCoeff (p := p) n j`. Rewrite using `[hz, Int.cast_mul, Int.cast_natCast]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (natCast_mem_pow (pow_dvd_factorial hn)))`.
-/
theorem sum_p_mul_logTermZero_sub_mem (hx : x ∈ RingHom.ker θ) {k M : ℕ} (hM : p * (p * k + 1) ≤ M) :
    ∑ j ∈ Finset.range M, (p : ACrisZero K p) * logTermZero hx j -
      ∑ n ∈ Finset.range M, logTermZero (one_add_pow_sub_one_mem hx) n ∈ 𝔭₀ ^ k := by
  have hpM : M ≤ p * M := Nat.le_mul_of_pos_left M hp.out.pos
  rw [Finset.sum_congr rfl fun n hn => logTermZero_one_add_pow hx n (p * M)
      (Nat.mul_le_mul_left p (Finset.mem_range.1 hn)),
    Finset.sum_congr rfl fun j _ => p_mul_logTermZero hx j]
  have h1 : ∀ j ∈ Finset.range M,
      ∑ n ∈ Finset.range (j + 1), (logCoeff p n j : ACrisZero K p) * dpowZero hx (j + 1) =
        ∑ n ∈ Finset.range M, (logCoeff p n j : ACrisZero K p) * dpowZero hx (j + 1) := by
    intro j hj
    apply Finset.sum_subset (Finset.range_subset_range.2 (Finset.mem_range.1 hj))
    intro n _ hn
    rw [Finset.mem_range, not_lt] at hn
    rw [logCoeff_of_lt (by omega), Int.cast_zero, zero_mul]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm (s := Finset.range M) (t := Finset.range (p * M)),
    ← Finset.sum_range_add_sum_Ico _ hpM, sub_add_cancel_left]
  refine neg_mem (Ideal.sum_mem _ fun j hj => Ideal.sum_mem _ fun n _ => ?_)
  have hj := (Finset.mem_Ico.1 hj).1
  by_cases hc : p * (n + 1) < j + 1
  · rw [logCoeff_of_gt hc, Int.cast_zero, zero_mul]
    exact zero_mem _
  · have hn : p * k ≤ n := by
      by_contra hlt
      have : p * (n + 1) ≤ p * (p * k) := Nat.mul_le_mul_left p (by omega)
      nlinarith
    obtain ⟨z, hz⟩ := factorial_dvd_logCoeff (p := p) n j
    rw [hz, Int.cast_mul, Int.cast_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (natCast_mem_pow (pow_dvd_factorial hn)))

/- English proof (translation)
Establish `hs` using `(isAdicSum_log hx).mul_left (algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p))`. Apply `log_eq_of_isAdicSum` to reduce the goal to its premises. Introduce `k`. Take `⟨N, hN⟩` from `hs k`. Use `⟨max N (p * (p * k + 1)), fun M hM => ?_⟩` and prove the remaining obligations.

Establish `h1` using `hN M (le_of_max_le_left hM)`. Establish `h2 : ∑ n ∈ Finset.range M, algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p) * logTerm hx n - ∑ n ∈ Finset.range M, logTerm (one_add_pow_sub_one_mem hx) n ∈ 𝔭 ^ k`. Establish `h` using `algebraMap_mem_pow (sum_p_mul_logTermZero_sub_mem hx (le_of_max_le_right hM))`. Rewrite `h` using `[map_sub, map_sum, map_sum]`. Simplify `h` using `only [map_mul, logTerm]`.

Use `add_mem h1 h2` as an intermediate fact. Simplify using `only at this`. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem log_one_add_pow (hx : x ∈ RingHom.ker θ) :
    log (one_add_pow_sub_one_mem hx) =
      algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p) * log hx := by
  have hs := (isAdicSum_log hx).mul_left (algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p))
  apply log_eq_of_isAdicSum
  intro k
  obtain ⟨N, hN⟩ := hs k
  refine ⟨max N (p * (p * k + 1)), fun M hM => ?_⟩
  have h1 := hN M (le_of_max_le_left hM)
  have h2 : ∑ n ∈ Finset.range M, algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p) *
      logTerm hx n - ∑ n ∈ Finset.range M, logTerm (one_add_pow_sub_one_mem hx) n ∈ 𝔭 ^ k := by
    have h := algebraMap_mem_pow (sum_p_mul_logTermZero_sub_mem hx (le_of_max_le_right hM))
    rw [map_sub, map_sum, map_sum] at h
    simpa only [map_mul, logTerm] using h
  have := add_mem h1 h2
  simp only at this
  rwa [sub_add_sub_cancel] at this

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem log_congr {x y : AInf K p} (h : x = y) (hx : x ∈ RingHom.ker θ) (hy : y ∈ RingHom.ker θ) :
    log hx = log hy := by
  subst h; rfl

/- English proof (translation)
Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]`. Conclude with `Ideal.mem_span_singleton_self _`.
-/
theorem span_p_le_comap_phi : 𝔭 ≤ Ideal.comap (phi K p) 𝔭 := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

/- English proof (translation)
Simplify using `only [logTermZero, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg, Subalgebra.coe_one, SubringClass.coe_natCast, coe_dpowZero]`.
-/
theorem coe_logTermZero {y : AInf K p} (hy : y ∈ RingHom.ker θ) (n : ℕ) :
    (logTermZero hy n : 𝔸) = (-1) ^ n * (n.factorial : 𝔸) * dpow (n + 1) y := by
  simp only [logTermZero, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg,
    Subalgebra.coe_one, SubringClass.coe_natCast, coe_dpowZero]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[coe_phiZero, coe_logTermZero, coe_logTermZero, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast, phiAway_dpow]`.
-/
theorem phiZero_logTermZero (hx : x ∈ RingHom.ker θ) (hφ : φ x ∈ RingHom.ker θ) (n : ℕ) :
    phiZero K p (logTermZero hx n) = logTermZero hφ n := by
  apply Subtype.ext
  rw [coe_phiZero, coe_logTermZero, coe_logTermZero, map_mul, map_mul, map_pow, map_neg, map_one,
    map_natCast, phiAway_dpow]

/- English proof (translation)
The claim follows from `phi_of y`.
-/
theorem phi_algebraMap_zero (y : ACrisZero K p) :
    phi K p (algebraMap (ACrisZero K p) (ACris K p) y) =
      algebraMap (ACrisZero K p) (ACris K p) (phiZero K p y) :=
  phi_of y

/- English proof (translation)
Rewrite using `[logTerm, logTerm, phi_algebraMap_zero, phiZero_logTermZero hx hφ]`.
-/
theorem phi_logTerm (hx : x ∈ RingHom.ker θ) (hφ : φ x ∈ RingHom.ker θ) (n : ℕ) :
    phi K p (logTerm hx n) = logTerm hφ n := by
  rw [logTerm, logTerm, phi_algebraMap_zero, phiZero_logTermZero hx hφ]

/- English proof (translation)
The claim follows from `(log_eq_of_isAdicSum (((isAdicSum_log hx).map (phi K p) span_p_le_comap_phi).congr (phi_logTerm hx hφ))).symm`.
-/
theorem phi_log (hx : x ∈ RingHom.ker θ) (hφ : φ x ∈ RingHom.ker θ) :
    phi K p (log hx) = log hφ :=
  (log_eq_of_isAdicSum (((isAdicSum_log hx).map (phi K p) span_p_le_comap_phi).congr
    (phi_logTerm hx hφ))).symm

/- English proof (translation)
Rewrite using `[AInf.mu, map_sub, map_one, WittVector.frobeniusEquiv_teichmuller, map_pow, add_sub_cancel]`.
-/
theorem frobenius_mu (ε : 𝒪♭) : φ (AInf.mu (K := K) ε) = (1 + AInf.mu ε) ^ p - 1 := by
  rw [AInf.mu, map_sub, map_one, WittVector.frobeniusEquiv_teichmuller, map_pow, add_sub_cancel]

/- English proof (translation)
Establish `hφ : φ (AInf.mu (K` using `K) ε) ∈ RingHom.ker θ := by`. Rewrite using `[frobenius_mu]`. Conclude with `one_add_pow_sub_one_mem (mu_mem_ker hε)`. Rewrite using `[periodT, phi_log _ hφ, log_congr (frobenius_mu ε) hφ (one_add_pow_sub_one_mem (mu_mem_ker hε)), log_one_add_pow]`.
-/
theorem phi_periodT {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) :
    phi K p (periodT hε) =
      algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p) * periodT hε := by
  have hφ : φ (AInf.mu (K := K) ε) ∈ RingHom.ker θ := by
    rw [frobenius_mu]; exact one_add_pow_sub_one_mem (mu_mem_ker hε)
  rw [periodT, phi_log _ hφ, log_congr (frobenius_mu ε) hφ (one_add_pow_sub_one_mem (mu_mem_ker hε)),
    log_one_add_pow]

/- English proof (translation)
Rewrite using `[phi_periodT, map_natCast]`.
-/
theorem phi_periodT_eq_mul {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) :
    phi K p (periodT hε) = (p : ACris K p) * periodT hε := by
  rw [phi_periodT, map_natCast]

/- English proof (translation)
Distinguish the cases in `hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) = 1`. Use `set ε' := (_root_.frobeniusEquiv 𝒪♭ p).symm ε`. Establish `hε' : ε = ε' ^ p`. Establish `h` using `(_root_.frobeniusEquiv 𝒪♭ p).apply_symm_apply ε`. Rewrite `h` using `[_root_.frobeniusEquiv_apply, frobenius_def]`.

Conclude with `h.symm`. Establish `hμ : AInf.mu (K` using `K) ε = φ (AInf.mu ε') := by`. Rewrite using `[frobenius_mu, AInf.mu, AInf.mu, hε', map_pow, add_sub_cancel]`. Establish `hφ : φ (AInf.mu (K` using `K) ε') ∈ RingHom.ker θ := hμ ▸ mu_mem_ker hε`. Establish `ht : periodT hε = algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p) * periodT (ε` using `ε') hζ := by`.

Rewrite using `[periodT, log_congr hμ _ hφ, ← phi_log (mu_mem_ker hζ) hφ, ← periodT, phi_periodT]`. Establish `hmem : periodT hε ∈ 𝔭`. Rewrite using `[ht]`. Conclude with `Ideal.mul_mem_right _ _ (by simpa using algebraMap_p_mem (K := K) (p := p))`. Conclude with `Ideal.pow_mem_of_mem _ hmem _ (Nat.sub_pos_of_lt hp.out.one_lt)`.

Conclude with `periodT_pow_mem hε hζ`.
-/
theorem periodT_pow_mem' {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : periodT hε ^ (p - 1) ∈ 𝔭 := by
  by_cases hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) = 1
  · set ε' := (_root_.frobeniusEquiv 𝒪♭ p).symm ε
    have hε' : ε = ε' ^ p := by
      have h := (_root_.frobeniusEquiv 𝒪♭ p).apply_symm_apply ε
      rw [_root_.frobeniusEquiv_apply, frobenius_def] at h
      exact h.symm
    have hμ : AInf.mu (K := K) ε = φ (AInf.mu ε') := by
      rw [frobenius_mu, AInf.mu, AInf.mu, hε', map_pow, add_sub_cancel]
    have hφ : φ (AInf.mu (K := K) ε') ∈ RingHom.ker θ := hμ ▸ mu_mem_ker hε
    have ht : periodT hε = algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p) *
        periodT (ε := ε') hζ := by
      rw [periodT, log_congr hμ _ hφ, ← phi_log (mu_mem_ker hζ) hφ, ← periodT, phi_periodT]
    have hmem : periodT hε ∈ 𝔭 := by
      rw [ht]
      exact Ideal.mul_mem_right _ _ (by simpa using algebraMap_p_mem (K := K) (p := p))
    exact Ideal.pow_mem_of_mem _ hmem _ (Nat.sub_pos_of_lt hp.out.one_lt)
  · exact periodT_pow_mem hε hζ

end PhiT

end ACris

end GroundTheory.PAdicHodge
