import Mathlib
import GroundTheory.LocalFields.PadicLogSeries

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Integer

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `hk' : k < m` using `by omega`. Establish `h1` using `Nat.choose_succ_right_eq (m - 1) k`.

Establish `hle : k ≤ m - 1` using `by omega`. Establish `h1' : (((m - 1).choose (k + 1) : ℕ) : ℤ) * (k + 1) = ((m - 1).choose k : ℕ) * ((m : ℤ) - 1 - k)`. Use `congrArg (fun t : ℕ ↦ (t : ℤ)) h1` as an intermediate fact. Simplify using `only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this`. Rewrite using `[this, Nat.cast_sub hle, Nat.cast_sub (by omega : 1 ≤ m)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨t, ht⟩` from `ih hk'`. Use `⟨((m : ℤ) - 1 - k) * t + (-1) ^ k * k.factorial, ?_⟩` and prove the remaining obligations. Establish `e1 : ((k + 1).factorial : ℤ) * ((((m - 1).choose (k + 1) : ℕ) : ℤ) - (-1) ^ (k + 1)) = (k.factorial : ℤ) * ((((m - 1).choose (k + 1) : ℕ) : ℤ) * (k + 1)) + (-1) ^ k * (k + 1) * k.factorial`.

Move the coercions through the operations in `[Nat.factorial_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, h1']`. Take the linear combination `((m : ℤ) - 1 - k) * ht`.
-/
theorem dvd_factorial_mul_choose_sub {m k : ℕ} (hk : k < m) :
    (m : ℤ) ∣ (k.factorial : ℤ) * (((m - 1).choose k : ℕ) - (-1) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < m := by omega
    have h1 := Nat.choose_succ_right_eq (m - 1) k
    have hle : k ≤ m - 1 := by omega
    have h1' : (((m - 1).choose (k + 1) : ℕ) : ℤ) * (k + 1) =
        ((m - 1).choose k : ℕ) * ((m : ℤ) - 1 - k) := by
      have := congrArg (fun t : ℕ ↦ (t : ℤ)) h1
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this
      rw [this, Nat.cast_sub hle, Nat.cast_sub (by omega : 1 ≤ m)]
      push_cast; ring
    obtain ⟨t, ht⟩ := ih hk'
    refine ⟨((m : ℤ) - 1 - k) * t + (-1) ^ k * k.factorial, ?_⟩
    have e1 : ((k + 1).factorial : ℤ) * ((((m - 1).choose (k + 1) : ℕ) : ℤ) - (-1) ^ (k + 1)) =
        (k.factorial : ℤ) * ((((m - 1).choose (k + 1) : ℕ) : ℤ) * (k + 1)) +
          (-1) ^ k * (k + 1) * k.factorial := by
      push_cast [Nat.factorial_succ]; ring
    rw [e1, h1']
    linear_combination ((m : ℤ) - 1 - k) * ht

end Integer

section Limit

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

omit [CharZero K] in
/- English proof (translation)
Rewrite using `[mem_valBall, neg_zero, WithZero.exp_zero, normalizedValuation_le_one_iff]`. Conclude with `intCast_mem _ z`.
-/
theorem intCast_mem_valBall_zero (z : ℤ) : (z : K) ∈ valBall K 0 := by
  rw [mem_valBall, neg_zero, WithZero.exp_zero, normalizedValuation_le_one_iff]
  exact intCast_mem _ z

omit [CharP 𝓀[K] p] [CharZero K] in

/- English proof (translation)
Use `set e := absRamificationIndex K`. Establish `h1` using `four_mul_padicValNat_le p e (Nat.succ_ne_zero k)`. Establish `h2 : N ≤ (N.toNat : ℤ)` using `Int.self_le_toNat N`. Establish `h3 : ((4 * N.toNat + 32 * e ^ 2 : ℕ) : ℤ) ≤ k` using `by exact_mod_cast hk`. Establish `h4 : ((4 * e * padicValNat p (k + 1) : ℕ) : ℤ) ≤ ((k + 1 + 32 * e ^ 2 : ℕ) : ℤ)`.

Conclude with `h1` after adjusting the coercions. Simplify using `only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h3 h4`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem logTerm_order_ge {N : ℤ} {k : ℕ} (hk : 4 * N.toNat + 32 * absRamificationIndex K ^ 2 ≤ k) :
    N ≤ (k + 1 : ℤ) - absRamificationIndex K * padicValNat p (k + 1) := by
  set e := absRamificationIndex K
  have h1 := four_mul_padicValNat_le p e (Nat.succ_ne_zero k)
  have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  have h3 : ((4 * N.toNat + 32 * e ^ 2 : ℕ) : ℤ) ≤ k := by exact_mod_cast hk
  have h4 : ((4 * e * padicValNat p (k + 1) : ℕ) : ℤ) ≤ ((k + 1 + 32 * e ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast h1
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h3 h4
  nlinarith

omit [CharZero K] in
/- English proof (translation)
Establish `h1 : padicValNat p j < p ^ padicValNat p j` using `Nat.lt_pow_self hp.out.one_lt`. Establish `h2 : p ^ padicValNat p j ≤ j` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hj) pow_padicValNat_dvd`. Use linear arithmetic over natural numbers and integers.
-/
theorem padicValNat_le_self' {j : ℕ} (hj : j ≠ 0) : padicValNat p j ≤ j := by
  have h1 : padicValNat p j < p ^ padicValNat p j := Nat.lt_pow_self hp.out.one_lt
  have h2 : p ^ padicValNat p j ≤ j := Nat.le_of_dvd (Nat.pos_of_ne_zero hj) pow_padicValNat_dvd
  omega

/- English proof (translation)
Rewrite using `[mem_valBall, Nat.cast_pow, map_pow, normalizedValuation_natCast_prime p, ← WithZero.exp_nsmul]`. Simplify using `[mul_comm]`.
-/
theorem natCast_prime_pow_mem_valBall (n : ℕ) :
    ((p ^ n : ℕ) : K) ∈ valBall K (absRamificationIndex K * n) := by
  rw [mem_valBall, Nat.cast_pow, map_pow, normalizedValuation_natCast_prime p,
    ← WithZero.exp_nsmul]
  simp [mul_comm]

/- English proof (translation)
Use `tendsto_zero_iff_valBall.mpr fun N ↦ ?_` and prove the remaining obligations. Rewrite using `[eventually_atTop]`. Use `⟨N.toNat, fun n hn ↦ valBall_antitone ?_ (natCast_prime_pow_mem_valBall p n)⟩` and prove the remaining obligations. Establish `he` using `one_le_absRamificationIndex (K := K) p`. Establish `h2 : N ≤ (N.toNat : ℤ)` using `Int.self_le_toNat N`.

Establish `h3 : (N.toNat : ℤ) ≤ n` using `by exact_mod_cast hn`. Establish `he' : (1 : ℤ) ≤ absRamificationIndex K` using `by exact_mod_cast he`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem tendsto_natCast_prime_pow : Tendsto (fun n : ℕ ↦ ((p ^ n : ℕ) : K)) atTop (𝓝 0) := by
  refine tendsto_zero_iff_valBall.mpr fun N ↦ ?_
  rw [eventually_atTop]
  refine ⟨N.toNat, fun n hn ↦ valBall_antitone ?_ (natCast_prime_pow_mem_valBall p n)⟩
  have he := one_le_absRamificationIndex (K := K) p
  have h2 : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  have h3 : (N.toNat : ℤ) ≤ n := by exact_mod_cast hn
  have he' : (1 : ℤ) ≤ absRamificationIndex K := by exact_mod_cast he
  nlinarith

omit [ValuativeRel K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Rewrite using `[tsum_eq_sum (s := Finset.range m)]`. Rewrite using `[add_comm, add_pow, Finset.sum_range_succ']`. Simplify using `only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]`. Rewrite using `[Finset.sum_div]`. Use `Finset.sum_congr rfl fun k hk ↦ ?_` and prove the remaining obligations.

Establish `h` using `Nat.add_one_mul_choose_eq (m - 1) k`. Rewrite `h` using `[Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)]`. Establish `h' : (m : K) * ((m - 1).choose k : ℕ) = ((m.choose (k + 1) : ℕ) : K) * (k + 1 : ℕ)`. Conclude with `h` after adjusting the coercions. Establish `hm' : (m : K) ≠ 0` using `Nat.cast_ne_zero.mpr hm`.

Establish `hk' : ((k + 1 : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-(x * x ^ k)) * h'`. Introduce `k hk`. Rewrite `hk` using `[Finset.mem_range, not_lt]`.

Rewrite using `[Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]`.
-/
theorem one_add_pow_sub_one_div_eq (x : K) {m : ℕ} (hm : m ≠ 0) :
    ((1 + x) ^ m - 1) / (m : K) =
      ∑' k : ℕ, (((m - 1).choose k : ℕ) : K) * (x ^ (k + 1) / ((k + 1 : ℕ) : K)) := by
  rw [tsum_eq_sum (s := Finset.range m)]
  · rw [add_comm, add_pow, Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
      add_sub_cancel_right]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have h := Nat.add_one_mul_choose_eq (m - 1) k
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)] at h
    have h' : (m : K) * ((m - 1).choose k : ℕ) = ((m.choose (k + 1) : ℕ) : K) * (k + 1 : ℕ) := by
      exact_mod_cast h
    have hm' : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hk' : ((k + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    field_simp
    linear_combination (-(x * x ^ k)) * h'
  · intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

end Limit

section Limit2

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

/- English proof (translation)
Rewrite using `[← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_valBall]`. Introduce `N`. Use `set e := absRamificationIndex K with he_def`. Use `set K0 := 4 * N.toNat + 32 * e ^ 2 with hK0`. Establish `he` using `one_le_absRamificationIndex (K := K) p`.

Rewrite using `[eventually_atTop]`. Use `⟨N.toNat + 2 * K0 + 1, fun n hn ↦ ?_⟩` and prove the remaining obligations. Establish `hm : p ^ n ≠ 0` using `pow_ne_zero _ hp.out.ne_zero`. Establish `hKm : K0 < p ^ n`. Establish `h1 : n < 2 ^ n` using `Nat.lt_two_pow_self`.

Establish `h2 : 2 ^ n ≤ p ^ n` using `Nat.pow_le_pow_left hp.out.two_le n`. Use linear arithmetic over natural numbers and integers. Establish `hs1 : Summable fun k : ℕ ↦ (((p ^ n - 1).choose k : ℕ) : K) * (x ^ (k + 1) / ((k + 1 : ℕ) : K))`. Use `summable_of_ne_finset_zero (s := Finset.range (p ^ n)) fun k hk ↦ ?_` and prove the remaining obligations. Rewrite `hk` using `[Finset.mem_range, not_lt]`.

Rewrite using `[Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]`. Establish `hs2` using `summable_logSeries p hx`. Rewrite using `[one_add_pow_sub_one_div_eq x hm, logSeries, ← hs1.tsum_sub hs2]`. Use `tsum_mem_valBall fun k ↦ ?_` and prove the remaining obligations. Use `set T : K := x ^ (k + 1) / ((k + 1 : ℕ) : K) with hT_def`.

Establish `hT : T ∈ valBall K ((k + 1 : ℕ) * 1 - e * padicValNat p (k + 1))` using `div_natCast_mem_valBall p (pow_mem_valBall hx (k + 1)) (Nat.succ_ne_zero k)`. Use `set C : ℕ := (p ^ n - 1).choose k`. Establish `heq : (C : K) * T - (-1) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K) = (((C : ℤ) - (-1) ^ k : ℤ) : K) * T`. Rewrite using `[hT_def]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Distinguish the cases in `hk : K0 ≤ k`. Establish `hmem` using `mul_mem_valBall (intCast_mem_valBall_zero ((C : ℤ) - (-1) ^ k)) hT`. Use `valBall_antitone ?_ hmem` and prove the remaining obligations.

Use `logTerm_order_ge (K := K) p hk` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Use `push Not at hk`. Take `⟨t, ht⟩` from `dvd_factorial_mul_choose_sub (m := p ^ n) (k := k) (by omega)`.

Establish `hkf : (k.factorial : K) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)`. Establish `hc : ((((C : ℤ) - (-1) ^ k : ℤ)) : K) = ((p ^ n : ℕ) : K) * (t : K) / k.factorial`. Rewrite using `[eq_div_iff hkf]`. Use `congrArg (fun z : ℤ ↦ (z : K)) ht` as an intermediate fact. Move the coercions through the operations in `at this ⊢`.

Take the linear combination `this`. Establish `h1 : ((p ^ n : ℕ) : K) * (t : K) ∈ valBall K (e * n + 0)` using `mul_mem_valBall (natCast_prime_pow_mem_valBall p n) (intCast_mem_valBall_zero t)`. Establish `h2` using `div_natCast_mem_valBall p h1 (Nat.factorial_ne_zero k)`. Rewrite `h2` using `[← hc]`. Use `valBall_antitone ?_ (mul_mem_valBall h2 hT)` and prove the remaining obligations.

Establish `hv1` using `padicValNat_le_self' (p := p) (Nat.succ_ne_zero k)`. Establish `hv2` using `padicValNat_factorial_le (p := p) k`. Establish `h2N : N ≤ (N.toNat : ℤ)` using `Int.self_le_toNat N`. Establish `hn' : ((N.toNat + 2 * K0 + 1 : ℕ) : ℤ) ≤ n` using `by exact_mod_cast hn`. Establish `hk' : (k : ℤ) < K0` using `by exact_mod_cast hk`.

Establish `hv1' : (padicValNat p (k + 1) : ℤ) ≤ k + 1` using `by exact_mod_cast hv1`. Establish `hv2' : (padicValNat p k.factorial : ℤ) ≤ k` using `by exact_mod_cast hv2`. Establish `he' : (1 : ℤ) ≤ e` using `by exact_mod_cast he`. Move the coercions through the operations in `at hn' ⊢`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hv1' (by positivity : (0 : ℤ) ≤ e), mul_le_mul_of_nonneg_left hv2' (by positivity : (0 : ℤ) ≤ e)]`.
-/
theorem tendsto_logSeries {x : K} (hx : x ∈ valBall K 1) :
    Tendsto (fun n : ℕ ↦ ((1 + x) ^ (p ^ n) - 1) / ((p ^ n : ℕ) : K)) atTop
      (𝓝 (logSeries x)) := by
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_valBall]
  intro N
  set e := absRamificationIndex K with he_def
  set K0 := 4 * N.toNat + 32 * e ^ 2 with hK0
  have he := one_le_absRamificationIndex (K := K) p
  rw [eventually_atTop]
  refine ⟨N.toNat + 2 * K0 + 1, fun n hn ↦ ?_⟩
  have hm : p ^ n ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hKm : K0 < p ^ n := by
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    have h2 : 2 ^ n ≤ p ^ n := Nat.pow_le_pow_left hp.out.two_le n
    omega
  have hs1 : Summable fun k : ℕ ↦ (((p ^ n - 1).choose k : ℕ) : K) *
      (x ^ (k + 1) / ((k + 1 : ℕ) : K)) := by
    refine summable_of_ne_finset_zero (s := Finset.range (p ^ n)) fun k hk ↦ ?_
    rw [Finset.mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  have hs2 := summable_logSeries p hx
  rw [one_add_pow_sub_one_div_eq x hm, logSeries, ← hs1.tsum_sub hs2]
  refine tsum_mem_valBall fun k ↦ ?_
  set T : K := x ^ (k + 1) / ((k + 1 : ℕ) : K) with hT_def
  have hT : T ∈ valBall K ((k + 1 : ℕ) * 1 - e * padicValNat p (k + 1)) :=
    div_natCast_mem_valBall p (pow_mem_valBall hx (k + 1)) (Nat.succ_ne_zero k)
  set C : ℕ := (p ^ n - 1).choose k
  have heq : (C : K) * T - (-1) ^ k * x ^ (k + 1) / ((k + 1 : ℕ) : K) =
      (((C : ℤ) - (-1) ^ k : ℤ) : K) * T := by
    rw [hT_def]; push_cast; ring
  rw [heq]
  by_cases hk : K0 ≤ k
  · have hmem := mul_mem_valBall (intCast_mem_valBall_zero ((C : ℤ) - (-1) ^ k)) hT
    refine valBall_antitone ?_ hmem
    have := logTerm_order_ge (K := K) p hk
    push_cast at this ⊢
    linarith
  · push Not at hk
    obtain ⟨t, ht⟩ := dvd_factorial_mul_choose_sub (m := p ^ n) (k := k) (by omega)
    have hkf : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hc : ((((C : ℤ) - (-1) ^ k : ℤ)) : K) = ((p ^ n : ℕ) : K) * (t : K) / k.factorial := by
      rw [eq_div_iff hkf]
      have := congrArg (fun z : ℤ ↦ (z : K)) ht
      push_cast at this ⊢
      linear_combination this
    have h1 : ((p ^ n : ℕ) : K) * (t : K) ∈ valBall K (e * n + 0) :=
      mul_mem_valBall (natCast_prime_pow_mem_valBall p n) (intCast_mem_valBall_zero t)
    have h2 := div_natCast_mem_valBall p h1 (Nat.factorial_ne_zero k)
    rw [← hc] at h2
    refine valBall_antitone ?_ (mul_mem_valBall h2 hT)
    have hv1 := padicValNat_le_self' (p := p) (Nat.succ_ne_zero k)
    have hv2 := padicValNat_factorial_le (p := p) k
    have h2N : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
    have hn' : ((N.toNat + 2 * K0 + 1 : ℕ) : ℤ) ≤ n := by exact_mod_cast hn
    have hk' : (k : ℤ) < K0 := by exact_mod_cast hk
    have hv1' : (padicValNat p (k + 1) : ℤ) ≤ k + 1 := by exact_mod_cast hv1
    have hv2' : (padicValNat p k.factorial : ℤ) ≤ k := by exact_mod_cast hv2
    have he' : (1 : ℤ) ≤ e := by exact_mod_cast he
    push_cast at hn' ⊢
    nlinarith [mul_le_mul_of_nonneg_left hv1' (by positivity : (0 : ℤ) ≤ e),
      mul_le_mul_of_nonneg_left hv2' (by positivity : (0 : ℤ) ≤ e)]

end Limit2

section Hom

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Rewrite using `[mem_unitFiltrationUnits_iff hn hϖ, mem_valBall, ← map_pow, ← normalizedValuation_le_iff, map_pow, normalizedValuation_uniformizer hϖ, ← WithZero.exp_nsmul]`. Simplify using the standard rewrite rules.
-/
theorem mem_unitFiltrationUnits_iff_valBall {n : ℕ} (hn : 1 ≤ n) {x : Kˣ} :
    x ∈ unitFiltrationUnits K n ↔ (x : K) - 1 ∈ valBall K n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [mem_unitFiltrationUnits_iff hn hϖ, mem_valBall, ← map_pow, ← normalizedValuation_le_iff,
    map_pow, normalizedValuation_uniformizer hϖ, ← WithZero.exp_nsmul]
  simp

/- English proof (translation)
Simplify using `using (mem_unitFiltrationUnits_iff_valBall le_rfl).mp u.2`.
-/
theorem sub_one_mem_valBall_one (u : unitFiltrationUnits K 1) :
    ((u : Kˣ) : K) - 1 ∈ valBall K 1 := by
  simpa using (mem_unitFiltrationUnits_iff_valBall le_rfl).mp u.2

variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

include p in

/- English proof (translation)
Establish `hz : (1 + x) * (1 + y) - 1 ∈ valBall K 1`. Establish `: (1 + x) * (1 + y) - 1 = x + y + x * y` using `by ring`. Rewrite using `[this]`. Conclude with `add_mem (add_mem hx hy) (valBall_antitone (by norm_num) (mul_mem_valBall hx hy))`. Establish `ha` using `tendsto_logSeries p hx`.

Establish `hb` using `tendsto_logSeries p hy`. Establish `hc` using `tendsto_logSeries p hz`. Establish `hm` using `tendsto_natCast_prime_pow (K := K) p`. Establish `key : ∀ n : ℕ, ((1 + ((1 + x) * (1 + y) - 1)) ^ (p ^ n) - 1) / ((p ^ n : ℕ) : K) = ((1 + x) ^ (p ^ n) - 1) / ((p ^ n : ℕ) : K) + ((1 + y) ^ (p ^ n) - 1) / ((p ^ n : ℕ) : K) + ((p ^ n : ℕ) : K) * (((1 + x) ^ (p ^ n) - 1) / ((p ^ n : ℕ) : K)) * (((1 + y) ^ (p ^ n) - 1) / ((p ^ n : …`. Introduce `n`.

Establish `h0 : ((p ^ n : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.out.ne_zero)`. Rewrite using `[add_sub_cancel, mul_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hlim` using `(ha.add hb).add ((hm.mul ha).mul hb)`.

Simplify using `only [zero_mul, add_zero] at hlim`. Conclude with `tendsto_nhds_unique (hc.congr key) hlim`.
-/
theorem logSeries_mul {x y : K} (hx : x ∈ valBall K 1) (hy : y ∈ valBall K 1) :
    logSeries ((1 + x) * (1 + y) - 1) = logSeries x + logSeries y := by
  have hz : (1 + x) * (1 + y) - 1 ∈ valBall K 1 := by
    have : (1 + x) * (1 + y) - 1 = x + y + x * y := by ring
    rw [this]
    exact add_mem (add_mem hx hy) (valBall_antitone (by norm_num) (mul_mem_valBall hx hy))
  have ha := tendsto_logSeries p hx
  have hb := tendsto_logSeries p hy
  have hc := tendsto_logSeries p hz
  have hm := tendsto_natCast_prime_pow (K := K) p
  have key : ∀ n : ℕ, ((1 + ((1 + x) * (1 + y) - 1)) ^ (p ^ n) - 1) / ((p ^ n : ℕ) : K) =
      ((1 + x) ^ (p ^ n) - 1) / ((p ^ n : ℕ) : K) + ((1 + y) ^ (p ^ n) - 1) / ((p ^ n : ℕ) : K) +
      ((p ^ n : ℕ) : K) * (((1 + x) ^ (p ^ n) - 1) / ((p ^ n : ℕ) : K)) *
        (((1 + y) ^ (p ^ n) - 1) / ((p ^ n : ℕ) : K)) := by
    intro n
    have h0 : ((p ^ n : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.out.ne_zero)
    rw [add_sub_cancel, mul_pow]
    field_simp
    ring
  have hlim := (ha.add hb).add ((hm.mul ha).mul hb)
  simp only [zero_mul, add_zero] at hlim
  exact tendsto_nhds_unique (hc.congr key) hlim

omit [CharP 𝓀[K] p] [CharZero K] in
/- English proof (translation)
Establish `hp2 : (2 : ℤ) ≤ p` using `by exact_mod_cast hp.out.two_le`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sub_one_le_of_lt {a : ℤ} (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) {b : ℤ}
    (hab : a ≤ b) : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * b := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
  nlinarith

/- English proof (translation)
Assume the negation of the conclusion as `hx0`. Establish `hv` using `normalizedValuation_eq_exp_ord hx0`. Establish `hxa : x ∈ valBall K (ord x)` using `by rw [mem_valBall, hv]`. Establish `hxa1 : x ∉ valBall K (ord x + 1)`. Rewrite using `[mem_valBall, hv, WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers. Establish `hra : r ≤ ord x`. Rewrite `hx` using `[mem_valBall, hv, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Use `logSeries_sub_self_mem p hxa (sub_one_le_of_lt p hr hra)` as an intermediate fact.

Rewrite `this` using `[h, zero_sub]`. Conclude with `hxa1 (by simpa using neg_mem this)`.
-/
theorem eq_zero_of_logSeries_eq_zero {r : ℤ} (hr : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * r)
    {x : K} (hx : x ∈ valBall K r) (h : logSeries x = 0) : x = 0 := by
  by_contra hx0
  have hv := normalizedValuation_eq_exp_ord hx0
  have hxa : x ∈ valBall K (ord x) := by rw [mem_valBall, hv]
  have hxa1 : x ∉ valBall K (ord x + 1) := by
    rw [mem_valBall, hv, WithZero.exp_le_exp]; omega
  have hra : r ≤ ord x := by
    rw [mem_valBall, hv, WithZero.exp_le_exp] at hx; omega
  have := logSeries_sub_self_mem p hxa (sub_one_le_of_lt p hr hra)
  rw [h, zero_sub] at this
  exact hxa1 (by simpa using neg_mem this)

end Hom

section PadicLog

variable (K) [CharZero K]

noncomputable def padicLog : Additive (unitFiltrationUnits K 1) →+ K where
  toFun u := logSeries ((((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ) : K) - 1)
  map_zero' := by simp [logSeries]
  map_add' u w := by
    have h := logSeries_mul (ringChar 𝓀[K]) (sub_one_mem_valBall_one (Additive.toMul u))
      (sub_one_mem_valBall_one (Additive.toMul w))
    simp only [add_sub_cancel] at h
    simpa only [toMul_add, Subgroup.coe_mul, Units.val_mul] using h

variable {K}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem padicLog_apply (u : Additive (unitFiltrationUnits K 1)) :
    padicLog K u = logSeries ((((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ) : K) - 1) :=
  rfl

end PadicLog

section PadicLogProps

variable [CharZero K]

/- English proof (translation)
Use `continuous_of_continuousAt_zero (padicLog K) ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_zero, tendsto_zero_iff_valBall]`. Introduce `N`. Use `set p := ringChar 𝓀[K]`. Use `set e := absRamificationIndex K`.

Establish `hp2 : (2 : ℤ) ≤ p` using `by exact_mod_cast (Fact.out : p.Prime).two_le`. Use `set r : ℕ := N.toNat + e + 1 with hr_def`. Establish `hr : (e : ℤ) < (p - 1 : ℤ) * (r : ℕ)`. Establish `: (e : ℤ) + 1 ≤ r` using `by rw [hr_def]; push_cast; omega`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hcont : Continuous fun u : Additive (unitFiltrationUnits K 1) ↦ ((((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ) : K) - 1)` using `(Units.continuous_val.comp (continuous_subtype_val.comp continuous_toMul)).sub continuous_const`. Establish `hopen` using `(isOpen_valBall (r : ℤ)).preimage hcont`. Use `filter_upwards [hopen.mem_nhds (by simp)] with u hu`. Use `valBall_antitone ?_ (logSeries_mem_valBall p hu hr)` and prove the remaining obligations. Rewrite using `[hr_def]`.

Use `push_cast`. Use `Int.self_le_toNat N` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem continuous_padicLog : Continuous (padicLog K) := by
  refine continuous_of_continuousAt_zero (padicLog K) ?_
  rw [ContinuousAt, map_zero, tendsto_zero_iff_valBall]
  intro N
  set p := ringChar 𝓀[K]
  set e := absRamificationIndex K
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  set r : ℕ := N.toNat + e + 1 with hr_def
  have hr : (e : ℤ) < (p - 1 : ℤ) * (r : ℕ) := by
    have : (e : ℤ) + 1 ≤ r := by rw [hr_def]; push_cast; omega
    nlinarith
  have hcont : Continuous fun u : Additive (unitFiltrationUnits K 1) ↦
      ((((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ) : K) - 1) :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_toMul)).sub
      continuous_const
  have hopen := (isOpen_valBall (r : ℤ)).preimage hcont
  filter_upwards [hopen.mem_nhds (by simp)] with u hu
  refine valBall_antitone ?_ (logSeries_mem_valBall p hu hr)
  rw [hr_def]; push_cast
  have := Int.self_le_toNat N
  omega

end PadicLogProps

end GroundTheory.LocalField
