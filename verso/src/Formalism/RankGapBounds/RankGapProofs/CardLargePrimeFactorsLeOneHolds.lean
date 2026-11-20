import Formalism.RankGapBounds.LargePrimeFactor

open Real Finset

namespace Formalism.RankGapBounds.ChebyshevFactorialBounds

/- English proof (authored)
Chebyshev's estimate bounds θ(n) by n log 4 for nonnegative n. Substitute the definition of θ(n) as the sum of log p over primes at most n.
-/
theorem chebyshevThetaLe_holds : ChebyshevTheta := by
  intro n
  have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  rw [Chebyshev.theta_eq_sum_primesLE_log] at h
  exact h

/- English proof (authored)
For each prime p at most n, the valuation of n factorial at p is at least ⌊n/p⌋, since the first summand in Legendre's formula is ⌊n/p⌋ and the others are nonnegative. The powers of distinct primes are pairwise coprime. Multiplying their separate divisibilities proves the claim.
-/
private theorem prod_primes_pow_div_dvd_factorial (n : ℕ) : ∏ p ∈ primesUpTo n, p ^ (n / p) ∣ n.factorial := by
  have key : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → ∏ p ∈ s, p ^ (n / p) ∣ n.factorial := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | @insert a s ha ih =>
      intro hs
      rw [Finset.prod_insert ha]
      have hpa : a.Prime := hs a (Finset.mem_insert_self a s)
      have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ (ih hs')
      · exact Nat.Coprime.prod_right fun p hp =>
          Nat.Coprime.pow _ _ ((Nat.coprime_primes hpa (hs' p hp)).mpr fun h => ha (h ▸ hp))
      · rw [hpa.pow_dvd_factorial_iff (show Nat.log a n < Nat.log a n + 2 by omega)]
        calc n / a = n / a ^ 1 := by rw [pow_one]
          _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log a n + 2), n / a ^ i :=
            Finset.single_le_sum (f := fun i => n / a ^ i) (fun _ _ => Nat.zero_le _)
              (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
  exact key _ fun p hp => (Finset.mem_filter.mp hp).2

/- English proof (authored)
The product of p raised to ⌊n/p⌋ over primes at most n divides n factorial, which is at most n raised to n. Taking logarithms gives a bound n log n for the sum with the floor weights. Since n/p ≤ ⌊n/p⌋ + 1, replacing the floors adds at most the sum of log p, bounded by n log 4. Divide the resulting inequality by the positive n.
-/
private theorem sum_primes_log_div_le_log_add_log_four (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ primesUpTo n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : ∀ p ∈ primesUpTo n, (0 : ℝ) < p := fun p hp => by
    exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  have h1 : ∑ p ∈ primesUpTo n, ((n / p : ℕ) : ℝ) * Real.log p ≤ (n : ℝ) * Real.log n := by
    have hd := Nat.le_of_dvd (Nat.factorial_pos n) (prod_primes_pow_div_dvd_factorial n)
    have hprod : (0 : ℝ) < ∏ p ∈ primesUpTo n, (p : ℝ) ^ (n / p) :=
      Finset.prod_pos fun p hp => pow_pos (hpos p hp) _
    calc ∑ p ∈ primesUpTo n, ((n / p : ℕ) : ℝ) * Real.log p
        = Real.log (∏ p ∈ primesUpTo n, (p : ℝ) ^ (n / p)) := by
          rw [Real.log_prod fun p hp => (pow_pos (hpos p hp) _).ne']
          simp only [Real.log_pow]
      _ ≤ Real.log (n.factorial : ℝ) := Real.log_le_log hprod (by exact_mod_cast hd)
      _ ≤ Real.log ((n : ℝ) ^ n) :=
          Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) (by exact_mod_cast Nat.factorial_le_pow n)
      _ = n * Real.log n := Real.log_pow _ _
  have h2 : ∑ p ∈ primesUpTo n, Real.log p ≤ Real.log 4 * n := chebyshevThetaLe_holds n
  have h3 : ∀ p ∈ primesUpTo n,
      (n : ℝ) * (Real.log p / p) ≤ ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by
    intro p hp
    have hlog : 0 ≤ Real.log p :=
      Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
    have hfl : (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
      rw [← Nat.floor_div_eq_div (K := ℝ)]
      exact (Nat.lt_floor_add_one _).le
    calc (n : ℝ) * (Real.log p / p) = (n : ℝ) / p * Real.log p := by ring
      _ ≤ (((n / p : ℕ) : ℝ) + 1) * Real.log p := mul_le_mul_of_nonneg_right hfl hlog
      _ = ((n / p : ℕ) : ℝ) * Real.log p + Real.log p := by ring
  have hsum : (n : ℝ) * ∑ p ∈ primesUpTo n, Real.log p / p ≤ n * (Real.log n + Real.log 4) := by
    rw [Finset.mul_sum]
    calc ∑ p ∈ primesUpTo n, (n : ℝ) * (Real.log p / p)
        ≤ ∑ p ∈ primesUpTo n, (((n / p : ℕ) : ℝ) * Real.log p + Real.log p) := Finset.sum_le_sum h3
      _ = ∑ p ∈ primesUpTo n, ((n / p : ℕ) : ℝ) * Real.log p + ∑ p ∈ primesUpTo n, Real.log p :=
          Finset.sum_add_distrib
      _ ≤ n * Real.log n + Real.log 4 * n := add_le_add h1 h2
      _ = n * (Real.log n + Real.log 4) := by ring
  exact le_of_mul_le_mul_left hsum hn'

/- English proof (authored)
For each p ≥ 2, the bound 1/(p − 1) ≤ 2/p holds, and log p is nonnegative. The prime sum is therefore at most twice the sum weighted by 1/p, hence at most 2(log n + log 4). Since n ≥ 2 and log 4 = 2 log 2, this is at most 6 log n.
-/
theorem sumLogDivPredLe_holds : MertensType := by
  refine ⟨6, fun n hn => ?_⟩
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hS := sum_primes_log_div_le_log_add_log_four n (by omega)
  have hterm : ∀ p ∈ primesUpTo n, Real.log p / ((p : ℝ) - 1) ≤ 2 * (Real.log p / p) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < p - 1)]
    have hd : 2 * (Real.log p / p) * (p - 1) - Real.log p = Real.log p * (p - 2) / p := by
      field_simp
      ring
    have : 0 ≤ Real.log p * (p - 2) / p := div_nonneg (mul_nonneg hlog (by linarith)) (by linarith)
    linarith
  calc ∑ p ∈ primesUpTo n, Real.log p / ((p : ℝ) - 1)
      ≤ ∑ p ∈ primesUpTo n, 2 * (Real.log p / p) := Finset.sum_le_sum hterm
    _ = 2 * ∑ p ∈ primesUpTo n, Real.log p / p := by rw [Finset.mul_sum]
    _ ≤ 2 * (Real.log n + Real.log 4) := by linarith
    _ ≤ 6 * Real.log n := by rw [h4]; linarith

/- English proof (authored)
If two different primes greater than L divided z, their coprimality would make their product divide z. The product would then be at most z, yet it exceeds L². This contradicts the bound on z.
-/
theorem cardLargePrimeFactorsLeOne_holds : LargePrimeFactor := by
  intro L z hL hz hzL
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Nat.mem_primeFactors] at ha hb
  by_contra hne
  have hab : a * b ∣ z := Nat.Coprime.mul_dvd_of_dvd_of_dvd
    ((Nat.coprime_primes ha.1.1 hb.1.1).mpr hne) ha.1.2.1 hb.1.2.1
  have hle : ((a * b : ℕ) : ℝ) ≤ z := by exact_mod_cast Nat.le_of_dvd (by omega) hab
  push_cast at hle
  have hLL : L * L < (a : ℝ) * b := mul_lt_mul'' ha.2 hb.2 hL hL
  rw [sq] at hzL
  linarith

/- English proof (authored)
The harmonic sum through n is the sum of the reciprocals of the integers from one to n. Apply the harmonic-number estimate Hₙ ≤ 1 + log n.
-/
theorem harmonicLeOneAddLog_holds : HarmonicLog := by
  intro n _
  have h := harmonic_le_one_add_log n
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  simpa only [one_div] using h

/- English proof (authored)
For modulus l > 0, let r be the remainder of a − 1 modulo l. Then 0 ≤ r < l, so r + 1 is a positive representative of the residue of a and is at most l. The set of positive representatives is therefore nonempty, and its least element is at most r + 1. If a is already in [1, l], it belongs to this set. Any smaller positive representative would differ from a by a positive multiple of l smaller than l, which is impossible.
-/
theorem leastPosResidueSpec_holds : LeastResFacts := by
  intro a l hl
  unfold leastRes
  set S := {d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ a - (d : ℤ)} with hS
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl
  have h0 : 0 ≤ (a - 1) % (l : ℤ) := Int.emod_nonneg _ hl'.ne'
  have hlt0 : (a - 1) % (l : ℤ) < l := Int.emod_lt_of_pos _ hl'
  set r := ((a - 1) % (l : ℤ)).toNat with hr
  have hr' : (r : ℤ) = (a - 1) % (l : ℤ) := Int.toNat_of_nonneg h0
  have hmemd : r + 1 ∈ S := by
    refine ⟨by omega, ?_⟩
    have he : a - ((r + 1 : ℕ) : ℤ) = (l : ℤ) * ((a - 1) / l) := by
      have := Int.emod_def (a - 1) (l : ℤ)
      push_cast
      linarith
    rw [he]
    exact dvd_mul_right _ _
  have hmem := Nat.sInf_mem ⟨_, hmemd⟩
  have hle : sInf S ≤ r + 1 := Nat.sInf_le hmemd
  have hrl : r < l := by omega
  refine ⟨hmem.1, by omega, hmem.2, fun ha1 hal => ?_⟩
  set m := a.toNat with hm
  have hm' : (m : ℤ) = a := Int.toNat_of_nonneg (by omega)
  have hamem : m ∈ S := ⟨by omega, by rw [hm', sub_self]; exact dvd_zero _⟩
  have h1 : sInf S ≤ m := Nat.sInf_le hamem
  have h2 : m ≤ sInf S := by
    by_contra hlt'
    rw [not_le] at hlt'
    obtain ⟨k, hk⟩ := hmem.2
    have hpos : 0 < a - ((sInf S : ℕ) : ℤ) := by omega
    have hsmall : a - ((sInf S : ℕ) : ℤ) < l := by have := hmem.1; omega
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · nlinarith
    · rw [hk0, mul_zero] at hk
      omega
    · nlinarith
  omega

end Formalism.RankGapBounds.ChebyshevFactorialBounds
