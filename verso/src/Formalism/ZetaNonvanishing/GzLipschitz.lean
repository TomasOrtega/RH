import Formalism.StatementU

open ArithmeticFunction

noncomputable section

namespace Formalism

namespace LogFactorialMertensBounds

def A (k : ℕ) : ℝ := ∑ n ∈ Finset.Ioc 0 k, Λ n / n

def P (k : ℕ) (x : ℝ) : ℝ :=
  x * A k - ∑ n ∈ Finset.Ioc 0 k, Λ n - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x

def K0 : ℝ := Real.log 4 + 7

/- English proof (authored)
The constant is log(4) + 7. Its logarithmic term is nonnegative because 4 ≥ 1.
-/
lemma lipschitzConst_nonneg : 0 ≤ K0 := by
  unfold K0
  have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
  linarith

/- English proof (authored)
For a natural number n, being at least 1 is equivalent to being positive. Both intervals also require n ≤ k.
-/
lemma Icc_one_eq_Ioc (k : ℕ) : Finset.Icc 1 k = Finset.Ioc 0 k := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/- English proof (authored)
For k = 0 the sum is empty and the factorial is 1, whose logarithm is zero. Passing from k to k + 1 adds log(k + 1) to the sum. The factorial is multiplied by k + 1, so its logarithm increases by the same amount.
-/
lemma sum_log_eq_log_factorial (k : ℕ) :
    ∑ n ∈ Finset.Ioc 0 k, Real.log n = Real.log (k.factorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le k), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k))]
    ring

/- English proof (authored)
Replace log(n) by the sum of the von Mangoldt function over the divisors of n. Reorder the finite sum by divisor d. For each d from 1 to k there are ⌊k/d⌋ positive multiples of d up to k, giving the stated weight.
-/
lemma sum_log_eq (k : ℕ) :
    ∑ n ∈ Finset.Ioc 0 k, Real.log n = ∑ n ∈ Finset.Ioc 0 k, Λ n * ((k / n : ℕ) : ℝ) := by
  have h1 : ∀ n ∈ Finset.Ioc 0 k, Real.log n = ∑ d ∈ n.divisors, Λ d :=
    fun n _ => ArithmeticFunction.vonMangoldt_sum.symm
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_comm' (t' := Finset.Ioc 0 k) (s' := fun d => (Finset.Ioc 0 k).filter (d ∣ ·))]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]
  · intro n d
    simp only [Finset.mem_Ioc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h0, hk⟩, hd, -⟩
      have hle := Nat.le_of_dvd h0 hd
      have hpos := Nat.pos_of_dvd_of_pos hd h0
      exact ⟨⟨⟨h0, hk⟩, hd⟩, hpos, by omega⟩
    · rintro ⟨⟨⟨h0, hk⟩, hd⟩, -, -⟩
      exact ⟨⟨h0, hk⟩, hd, by omega⟩

/- English proof (authored)
Multiply the weighted sum A(k) by k and bound k/n by ⌊k/n⌋ + 1. The coefficients are nonnegative, so the resulting upper bound is log(k!) plus the sum of the von Mangoldt function up to k. The factorial bound k! ≤ k to the power k and Chebyshev's bound on the latter sum give k times log(k) + log(4) + 4, with all three terms inside the factor. Divide by k > 0.
-/
lemma mertens_upper (k : ℕ) (hk : 1 ≤ k) : A k ≤ Real.log k + (Real.log 4 + 4) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hpsi : ∑ n ∈ Finset.Ioc 0 k, Λ n ≤ (Real.log 4 + 4) * k := by
    have h := Chebyshev.psi_le_const_mul_self (x := (k:ℝ)) hk0.le
    simpa [Chebyshev.psi] using h
  have hfact : Real.log (k.factorial : ℝ) ≤ k * Real.log k := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.factorial_le_pow k)
  have hmain : (k:ℝ) * A k ≤ ∑ n ∈ Finset.Ioc 0 k, Λ n * ((k / n : ℕ) : ℝ) +
      ∑ n ∈ Finset.Ioc 0 k, Λ n := by
    rw [A, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hnpos : 0 < n := hn.1
    have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
    have h1N : k < (k / n + 1) * n := by
      rw [Nat.add_mul, one_mul]
      exact Nat.lt_div_mul_add hnpos
    have h1R : (k:ℝ) ≤ (((k / n : ℕ) : ℝ) + 1) * n := by exact_mod_cast h1N.le
    have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have h2 : (k:ℝ) / n ≤ ((k / n : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hnR]
      exact h1R
    have h3 : (k:ℝ) * (Λ n / n) = Λ n * ((k:ℝ) / n) := by ring
    rw [h3]
    nlinarith [mul_le_mul_of_nonneg_left h2 hΛ]
  rw [← sum_log_eq, sum_log_eq_log_factorial] at hmain
  have h4 : (k:ℝ) * A k ≤ k * (Real.log k + (Real.log 4 + 4)) := by nlinarith
  exact le_of_mul_le_mul_left h4 hk0

/- English proof (authored)
The integer quotient ⌊k/n⌋ is at most k/n, so the divisor form for log(k!) is bounded above by kA(k). The k-th term of the series for exp(k) is k to the power k divided by k!. Taking logarithms of the bound by exp(k) gives k log(k) − k ≤ log(k!). Combine the bounds and divide by k.
-/
lemma mertens_lower (k : ℕ) (hk : 1 ≤ k) : Real.log k - 1 ≤ A k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hfl : Real.log (k.factorial : ℝ) ≤ k * A k := by
    rw [← sum_log_eq_log_factorial, sum_log_eq, A, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    have hd : ((k / n : ℕ) : ℝ) ≤ (k:ℝ) / n := Nat.cast_div_le
    have h3 : (k:ℝ) * (Λ n / n) = Λ n * ((k:ℝ) / n) := by ring
    rw [h3]
    exact mul_le_mul_of_nonneg_left hd hΛ
  have hst : k * Real.log k - k ≤ Real.log (k.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (k:ℝ) hk0.le k
    have hpos : (0:ℝ) < (k:ℝ) ^ k / k.factorial := by positivity
    have h2 := Real.log_le_log hpos h
    rw [Real.log_exp, Real.log_div (by positivity) (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)),
      Real.log_pow] at h2
    linarith
  have h5 : (k:ℝ) * (Real.log k - 1) ≤ k * A k := by nlinarith
  exact le_of_mul_le_mul_left h5 hk0

/- English proof (authored)
On k ≤ x < k + 1, the floor is k. Split each summand into x times its von Mangoldt coefficient divided by n minus the coefficient. At the endpoint x = k + 1 the floor adds the index k + 1, whose weight x/(k + 1) − 1 is zero. The formula holds on the closed interval.
-/
lemma Sz_eq (k : ℕ) (x : ℝ) (hx1 : (k:ℝ) ≤ x) (hx2 : x ≤ k + 1) :
    Sz x = x * A k - ∑ n ∈ Finset.Ioc 0 k, Λ n := by
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg k) hx1
  have key : ∀ k' : ℕ, ∑ n ∈ Finset.Icc 1 k', Λ n * (x / n - 1) =
      x * A k' - ∑ n ∈ Finset.Ioc 0 k', Λ n := by
    intro k'
    rw [Icc_one_eq_Ioc, A, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  unfold Sz
  rcases lt_or_eq_of_le hx2 with h | h
  · rw [show ⌊x⌋₊ = k from (Nat.floor_eq_iff hx0).2 ⟨hx1, h⟩, key]
  · subst h
    have hf : ⌊(k:ℝ) + 1⌋₊ = k + 1 := by
      rw [← Nat.cast_add_one, Nat.floor_natCast]
    have hone : ((k:ℝ) + 1) / (((k + 1 : ℕ)) : ℝ) = 1 := by
      push_cast
      exact div_self (by positivity)
    rw [hf, Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), key, hone]
    ring

/- English proof (authored)
The prime-sum error subtracts x log(x) and adds the linear Euler constant correction to the weighted sum. Substituting the closed-interval expression for that sum gives the stated piece.
-/
lemma Gz_eq_P (k : ℕ) (x : ℝ) (hx1 : (k:ℝ) ≤ x) (hx2 : x ≤ k + 1) : Gz x = P k x := by
  unfold Gz P
  rw [Sz_eq k x hx1 hx2]

/- English proof (authored)
Differentiate the affine part and the term −x log(x) at x > 0. The latter contributes −log(x) − 1, and the linear correction contributes 1 plus Euler's constant. Their constant terms cancel except for Euler's constant.
-/
lemma hasDerivAt_P (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (P k) (A k - Real.log x + Real.eulerMascheroniConstant) x := by
  have h1 := ((((hasDerivAt_id' (x := x)).mul_const (A k)).sub_const
    (∑ n ∈ Finset.Ioc 0 k, Λ n)).sub (Real.hasDerivAt_mul_log hx.ne')).add
    ((hasDerivAt_id' (x := x)).const_mul (1 + Real.eulerMascheroniConstant))
  refine (h1.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp only [P, Pi.add_apply, Pi.sub_apply]

/- English proof (authored)
If k = 0, the weighted sum is zero and x ranges from 1/2 to 1, so log(x) lies between −log(2) and zero. If k ≥ 1, the bounds on the weighted sum apply, and k ≤ x ≤ k + 1 ≤ 2k puts log(x) between log(k) and log(k) + log(2). Combining these inequalities in each case with 1/2 < γ < 2/3 and log(2) < 0.9 gives the absolute bound log(4) + 7.
-/
lemma deriv_bound (k : ℕ) (x : ℝ) (hx1 : (k:ℝ) ≤ x) (hx1' : 1 / 2 ≤ x) (hx2 : x ≤ k + 1) :
    |A k - Real.log x + Real.eulerMascheroniConstant| ≤ K0 := by
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hl4 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  unfold K0
  rw [abs_le]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hA : A 0 = 0 := by simp [A]
    have hx1'' : x ≤ 1 := by simpa using hx2
    have hlx : Real.log x ≤ 0 := Real.log_nonpos (by linarith) hx1''
    have hlx2 : Real.log (1 / 2) ≤ Real.log x := Real.log_le_log (by norm_num) hx1'
    rw [one_div, Real.log_inv] at hlx2
    rw [hA]
    constructor <;> linarith
  · have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hup := mertens_upper k hk
    have hlo := mertens_lower k hk
    have h1 : Real.log k ≤ Real.log x := Real.log_le_log (by linarith) hx1
    have h2 : Real.log x ≤ Real.log (2 * k) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul two_ne_zero (by positivity)] at h2
    constructor <;> linarith

/- English proof (authored)
On the interval from max(k, 1/2) to k + 1 the error agrees with the differentiable piece. Its derivative is bounded in absolute value by the same constant throughout this interval. Apply the mean value inequality between x and y.
-/
lemma lip_piece (k : ℕ) (x y : ℝ) (hx1 : (k:ℝ) ≤ x) (hx1' : 1 / 2 ≤ x) (hx2 : x ≤ k + 1)
    (hy1 : (k:ℝ) ≤ y) (hy1' : 1 / 2 ≤ y) (hy2 : y ≤ k + 1) :
    |Gz y - Gz x| ≤ K0 * |y - x| := by
  have hs : Convex ℝ (Set.Icc (max (k:ℝ) (1 / 2)) (k + 1)) := convex_Icc _ _
  have hder : ∀ t ∈ Set.Icc (max (k:ℝ) (1 / 2)) (k + 1),
      HasDerivWithinAt (P k) (A k - Real.log t + Real.eulerMascheroniConstant)
        (Set.Icc (max (k:ℝ) (1 / 2)) (k + 1)) t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right (k:ℝ) (1 / 2)) ht.1)
    exact (hasDerivAt_P k htpos).hasDerivWithinAt
  have hb : ∀ t ∈ Set.Icc (max (k:ℝ) (1 / 2)) (k + 1),
      ‖A k - Real.log t + Real.eulerMascheroniConstant‖ ≤ K0 := by
    intro t ht
    rw [Real.norm_eq_abs]
    exact deriv_bound k t (le_trans (le_max_left _ _) ht.1) (le_trans (le_max_right _ _) ht.1) ht.2
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hb hs
    ⟨max_le hx1 hx1', hx2⟩ ⟨max_le hy1 hy1', hy2⟩
  rw [Gz_eq_P k x hx1 hx2, Gz_eq_P k y hy1 hy2]
  simpa [Real.norm_eq_abs] using h

/- English proof (authored)
Induct on the upper integer endpoint, starting with the interval from 1/2 to 1. When the interval is extended by one unit, pairs in the old interval satisfy the induction hypothesis, and pairs in the new piece satisfy its derivative bound. For a pair on opposite sides of the joining point, split the difference there and apply the triangle inequality. The two lengths add to the original distance.
-/
lemma lip_upto (k : ℕ) : ∀ x y : ℝ, 1 / 2 ≤ x → x ≤ k + 1 → 1 / 2 ≤ y → y ≤ k + 1 →
    |Gz y - Gz x| ≤ K0 * |y - x| := by
  have hK := lipschitzConst_nonneg
  induction k with
  | zero =>
    intro x y hx1 hx2 hy1 hy2
    exact lip_piece 0 x y (by rw [Nat.cast_zero]; linarith) hx1 hx2
      (by rw [Nat.cast_zero]; linarith) hy1 hy2
  | succ k ih =>
    intro x y hx1 hx2 hy1 hy2
    push_cast at hx2 hy2
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have split : ∀ u v : ℝ, 1 / 2 ≤ u → u ≤ k + 1 → k + 1 ≤ v → v ≤ k + 1 + 1 →
        |Gz v - Gz u| ≤ K0 * |v - u| := by
      intro u v hu1 hu2 hv1 hv2
      have e1 := ih u (k + 1) hu1 hu2 (by linarith) le_rfl
      have e2 := lip_piece (k + 1) (k + 1 : ℝ) v (by push_cast; linarith) (by linarith)
        (by push_cast; linarith) (by push_cast; linarith) (by linarith) (by push_cast; linarith)
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ k + 1 - u)] at e1
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ v - (k + 1))] at e2
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ v - u)]
      calc |Gz v - Gz u| ≤ |Gz v - Gz (k + 1)| + |Gz (k + 1) - Gz u| := abs_sub_le _ _ _
        _ ≤ K0 * (v - (k + 1)) + K0 * (k + 1 - u) := add_le_add e2 e1
        _ = K0 * (v - u) := by ring
    rcases le_total x (k + 1) with hxk | hxk <;> rcases le_total y (k + 1) with hyk | hyk
    · exact ih x y hx1 hxk hy1 hyk
    · exact split x y hx1 hxk hyk hy2
    · have h := split y x hy1 hyk hxk hx2
      rwa [abs_sub_comm (Gz x), abs_sub_comm x] at h
    · exact lip_piece (k + 1) x y (by push_cast; linarith) hx1 (by push_cast; linarith)
        (by push_cast; linarith) hy1 (by push_cast; linarith)

end LogFactorialMertensBounds

open LogFactorialMertensBounds in
/- English proof (authored)
Any two points at least 1/2 lie in one of the bounded intervals covered by the preceding estimate, so the same Lipschitz constant works for every pair. Compare each value at t with the value at 1/2. The bound on the difference gives an upper bound of K₀(t − 1/2) plus the absolute value of the error at 1/2. Since t ≥ 1/2, the larger constant K₀ plus twice that absolute value controls both the linear growth and the differences.
-/
theorem zetaPrimeSumErrorLipschitz : GzLipschitz := by
  have hK := lipschitzConst_nonneg
  have hlip : ∀ a b : ℝ, 1 / 2 ≤ a → 1 / 2 ≤ b → |Gz a - Gz b| ≤ K0 * |a - b| := by
    intro a b ha hb
    exact lip_upto (⌊a⌋₊ + ⌊b⌋₊) b a hb
      (by push_cast; linarith [Nat.lt_floor_add_one b, Nat.cast_nonneg (α := ℝ) ⌊a⌋₊]) ha
      (by push_cast; linarith [Nat.lt_floor_add_one a, Nat.cast_nonneg (α := ℝ) ⌊b⌋₊])
  refine ⟨K0 + 2 * |Gz (1 / 2)|, fun t t' ht ht' => ⟨?_, ?_⟩⟩
  · have h := hlip t (1 / 2) ht le_rfl
    have h2 : |Gz t| ≤ |Gz t - Gz (1 / 2)| + |Gz (1 / 2)| := by
      have := abs_sub_abs_le_abs_sub (Gz t) (Gz (1 / 2))
      linarith
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t - 1 / 2)] at h
    nlinarith [abs_nonneg (Gz (1 / 2)), mul_nonneg (abs_nonneg (Gz (1 / 2))) (by linarith : (0:ℝ) ≤ t - 1 / 2)]
  · exact le_trans (hlip t t' ht ht')
      (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg (Gz (1 / 2))]) (abs_nonneg _))

end Formalism
