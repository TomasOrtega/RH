import Formalism.RankGapBounds.RandomSubsetCounterexample

namespace Formalism.RankGapBounds.LocalQuadraticParts

/- English proof (authored)
The residue of x equals one exactly when the residue of x − 1 is zero. This is equivalent to divisibility of x − 1 by n.
-/
lemma zmod_int_eq_one_iff (n : ℕ) (x : ℤ) : ((x : ZMod n) = 1) ↔ (n : ℤ) ∣ x - 1 := by
  rw [← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]

/- English proof (authored)
The residue of x equals minus one exactly when x + 1 has residue zero, equivalently when n divides x + 1.
-/
lemma zmod_int_eq_neg_one_iff (n : ℕ) (x : ℤ) : ((x : ZMod n) = -1) ↔ (n : ℤ) ∣ x + 1 := by
  rw [← sub_eq_zero, sub_neg_eq_add, ← Int.cast_one, ← Int.cast_add, ZMod.intCast_zmod_eq_zero_iff_dvd]

/- English proof (authored)
View l as an integer and apply the congruence criterion for residue one. Its residue modulo n is the same whether it is taken directly from the natural numbers or through the integers.
-/
lemma zmod_nat_eq_one_iff (n l : ℕ) : ((l : ZMod n) = 1) ↔ (n : ℤ) ∣ (l : ℤ) - 1 := by
  have h := zmod_int_eq_one_iff n (l : ℤ)
  simpa using h

/- English proof (authored)
View l as an integer and apply the congruence criterion for residue minus one. Both interpretations give the same residue modulo n.
-/
lemma zmod_nat_eq_neg_one_iff (n l : ℕ) : ((l : ZMod n) = -1) ↔ (n : ℤ) ∣ (l : ℤ) + 1 := by
  have h := zmod_int_eq_neg_one_iff n (l : ℤ)
  simpa using h

/- English proof (authored)
Write y = 2k + 1. Then y² + 1 = 4(k² + k) + 2, which has remainder two modulo four.
-/
lemma four_not_dvd_odd_sq_add_one (y : ℤ) (hy : Odd y) : ¬ (4 : ℤ) ∣ y ^ 2 + 1 := by
  obtain ⟨k, rfl⟩ := hy
  have h : (2 * k + 1) ^ 2 + 1 = 4 * (k ^ 2 + k) + 2 := by ring
  rw [h]
  generalize k ^ 2 + k = t
  omega

/- English proof (authored)
Write x = 2k + 1. Cancelling the visible powers of two reduces the left side to divisibility of k(k + 1) by 2 raised to m − 1, and the right side to divisibility of one of k or k + 1 by that power. Exactly one of the consecutive factors is odd, so it is coprime to the power of two. This proves the forward implication, and divisibility of either factor plainly implies divisibility of the product.
-/
lemma sq_sub_one_dvd_iff (x : ℤ) (hx : Odd x) (m : ℕ) (hm : 1 ≤ m) :
    (2 : ℤ) ^ (m + 1) ∣ x ^ 2 - 1 ↔ ((2 : ℤ) ^ m ∣ x - 1 ∨ (2 : ℤ) ^ m ∣ x + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨k, rfl⟩ := hx
  have e1 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by ring
  have e2 : 2 * k + 1 - 1 = 2 * k := by ring
  have e3 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
  have p1 : (2 : ℤ) ^ (n + 1 + 1) = 4 * 2 ^ n := by ring
  have p2 : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
  rw [e1, e2, e3, p1, p2, mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0),
    mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0), mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)]
  constructor
  · intro h
    rcases Int.even_or_odd k with ⟨b, hb⟩ | ⟨b, hb⟩
    · left
      have hc : IsCoprime ((2 : ℤ) ^ n) (k + 1) := by
        apply IsCoprime.pow_left
        refine ⟨-b, 1, ?_⟩
        rw [hb]
        ring
      exact hc.dvd_of_dvd_mul_right h
    · right
      have hc : IsCoprime ((2 : ℤ) ^ n) k := by
        apply IsCoprime.pow_left
        refine ⟨-b, 1, ?_⟩
        rw [hb]
        ring
      exact hc.dvd_of_dvd_mul_left h
  · rintro (h | h)
    · exact dvd_mul_of_dvd_left h _
    · exact dvd_mul_of_dvd_right h _

/- English proof (authored)
At j = 0 the statement is unchanged on both sides. For the induction step put y = x raised to 2ʲ, which is odd. The new modulus is a multiple of four, so it cannot divide y² + 1. By the odd-square divisibility criterion, it divides y² − 1 exactly when the previous modulus divides y − 1 or y + 1. Apply the induction hypothesis.
-/
lemma pow_two_pow_pm_iff (j : ℕ) : ∀ (x : ℤ), Odd x → ∀ m : ℕ, 1 ≤ m →
    (((2 : ℤ) ^ (m + j) ∣ x ^ (2 ^ j) - 1 ∨ (2 : ℤ) ^ (m + j) ∣ x ^ (2 ^ j) + 1) ↔
      ((2 : ℤ) ^ m ∣ x - 1 ∨ (2 : ℤ) ^ m ∣ x + 1)) := by
  induction j with
  | zero => intro x _ m _; simp
  | succ j ih =>
    intro x hx m hm
    have hy : Odd (x ^ (2 ^ j)) := hx.pow
    have hpow : x ^ (2 ^ (j + 1)) = (x ^ (2 ^ j)) ^ 2 := by rw [pow_succ, pow_mul]
    have hnot : ¬ (2 : ℤ) ^ (m + (j + 1)) ∣ (x ^ (2 ^ j)) ^ 2 + 1 := by
      intro h
      apply four_not_dvd_odd_sq_add_one _ hy
      refine dvd_trans ?_ h
      have : (4 : ℤ) = 2 ^ 2 := by norm_num
      rw [this]
      exact pow_dvd_pow 2 (by omega)
    rw [hpow, ← ih x hx m hm, show m + (j + 1) = m + j + 1 by omega,
      ← sq_sub_one_dvd_iff _ hy (m + j) (by omega)]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd h (by rw [show m + j + 1 = m + (j + 1) by omega]; exact hnot)
    · intro h
      exact Or.inl h

/- English proof (authored)
In the preceding power-of-two criterion take the base exponent to be e + 2 − j. It is positive by j ≤ e, and adding j restores e + 2.
-/
lemma pm_iff (e j : ℕ) (hj : j ≤ e) (x : ℤ) (hx : Odd x) :
    (((2 : ℤ) ^ (e + 2) ∣ x ^ (2 ^ j) - 1 ∨ (2 : ℤ) ^ (e + 2) ∣ x ^ (2 ^ j) + 1) ↔
      ((2 : ℤ) ^ (e + 2 - j) ∣ x - 1 ∨ (2 : ℤ) ^ (e + 2 - j) ∣ x + 1)) := by
  have h := pow_two_pow_pm_iff j x hx (e + 2 - j) (by omega)
  rw [show e + 2 - j + j = e + 2 by omega] at h
  exact h

/- English proof (authored)
An even integer exponent gives the identity, and an odd exponent gives minus one. Conversely the exponents zero and one yield these two values.
-/
lemma units_zpow_neg_one_iff (n : ℕ) (u : (ZMod n)ˣ) :
    (∃ k : ℤ, (-1 : (ZMod n)ˣ) ^ k = u) ↔ (u = 1 ∨ u = -1) := by
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd k with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero _⟩
    · exact ⟨1, zpow_one _⟩

/- English proof (authored)
The power of the quotient class is the class of the corresponding power of the original unit. This class is the identity exactly when the power belongs to the subgroup generated by minus one. That subgroup consists of one and minus one, and the inclusion of units into the residue ring distinguishes their values whenever they are distinct.
-/
lemma hOf_pow_eq_one_iff (e j l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) :
    (hOf e l hl) ^ (2 ^ j) = 1 ↔
      ((((l : ℤ) ^ (2 ^ j) : ℤ) : ZMod (4 * 2 ^ e)) = 1 ∨
        (((l : ℤ) ^ (2 ^ j) : ℤ) : ZMod (4 * 2 ^ e)) = -1) := by
  unfold hOf
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff,
    units_zpow_neg_one_iff]
  have hv : ((ZMod.unitOfCoprime l hl ^ (2 ^ j) : (ZMod (4 * 2 ^ e))ˣ) : ZMod (4 * 2 ^ e)) =
      (((l : ℤ) ^ (2 ^ j) : ℤ) : ZMod (4 * 2 ^ e)) := by
    simp [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
  constructor
  · rintro (h | h)
    · left
      rw [← hv, h, Units.val_one]
    · right
      rw [← hv, h, Units.val_neg, Units.val_one]
  · rintro (h | h)
    · left
      apply Units.ext
      rw [hv, h, Units.val_one]
    · right
      apply Units.ext
      rw [hv, h, Units.val_neg, Units.val_one]

/- English proof (authored)
The modulus is divisible by two. If l were even, the common divisor two would contradict coprimality. Hence l is odd.
-/
lemma odd_of_coprime (e l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) : Odd (l : ℤ) := by
  have h2 : ¬ 2 ∣ l := fun h => by
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h hl)
      (dvd_mul_of_dvd_left (by norm_num) _)
    omega
  exact Int.odd_iff.mpr (by omega)

/- English proof (authored)
The quotient power equals one exactly when the integer power of l is congruent to one or minus one modulo 2 raised to e + 2. The coprimality hypothesis makes l odd. Apply the power-of-two divisibility criterion and convert the resulting divisibilities back to congruences.
-/
theorem powTwoPowEqOneIff_holds : OrdersIff := by
  intro e j l hl hj
  rw [hOf_pow_eq_one_iff, zmod_int_eq_one_iff, zmod_int_eq_neg_one_iff, zmod_nat_eq_one_iff,
    zmod_nat_eq_neg_one_iff]
  push_cast
  rw [show (4 : ℤ) * 2 ^ e = 2 ^ (e + 2) by ring]
  exact pm_iff e j hj l (odd_of_coprime e l hl)

/- English proof (authored)
An odd l is congruent to one or minus one modulo four. The power criterion at j = e therefore shows that the order divides 2ᵉ, so it is 2ᵏ for some k ≤ e. Apply the criterion at k to see that 2 raised to e + 2 − k divides l − 1 or l + 1. Both are positive under the hypotheses, so l + 1 is at least that power. Since J is at least the order 2ᵏ, the same lower bound implies l + 1 ≥ (4 times 2ᵉ)/J.
-/
theorem leOfOrderOfLe_holds : OrdersBound := by
  intro e J l hl hJ hl1 hord
  have hodd := odd_of_coprime e l hl
  have hE : (hOf e l hl) ^ (2 ^ e) = 1 := by
    rw [powTwoPowEqOneIff_holds e e l hl le_rfl, show e + 2 - e = 2 by omega, zmod_nat_eq_one_iff,
      zmod_nat_eq_neg_one_iff]
    obtain ⟨k, hk⟩ := hodd
    push_cast
    rcases Int.even_or_odd k with ⟨b, hb⟩ | ⟨b, hb⟩
    · left
      rw [hk, hb]
      exact ⟨b, by ring⟩
    · right
      rw [hk, hb]
      exact ⟨b + 1, by ring⟩
  obtain ⟨k, hk, hko⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hE)
  have hk1 : (hOf e l hl) ^ (2 ^ k) = 1 := by
    rw [← hko]
    exact pow_orderOf_eq_one _
  have hres := (powTwoPowEqOneIff_holds e k l hl hk).mp hk1
  rw [zmod_nat_eq_one_iff, zmod_nat_eq_neg_one_iff] at hres
  have hM : ((2 : ℤ) ^ (e + 2 - k)) ≤ (l : ℤ) + 1 := by
    rcases hres with h | h
    · push_cast at h
      have hpos : (0 : ℤ) < l - 1 := by omega
      have := Int.le_of_dvd hpos h
      linarith
    · push_cast at h
      have hpos : (0 : ℤ) < l + 1 := by omega
      have := Int.le_of_dvd hpos h
      linarith
  have hJn : 2 ^ k ≤ J := hko ▸ hord
  have hJ' : (2 : ℝ) ^ k ≤ J := by exact_mod_cast hJn
  have key : (4 * 2 ^ e : ℝ) = 2 ^ (e + 2 - k) * 2 ^ k := by
    rw [← pow_add, show e + 2 - k + k = e + 2 by omega]
    ring
  have h1 : (4 * 2 ^ e : ℝ) / J ≤ 4 * 2 ^ e / 2 ^ k :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hJ'
  have h2 : (4 * 2 ^ e : ℝ) / 2 ^ k = 2 ^ (e + 2 - k) := by
    rw [key]
    field_simp
  have h3 : (2 : ℝ) ^ (e + 2 - k) ≤ l + 1 := by exact_mod_cast hM
  linarith

end Formalism.RankGapBounds.LocalQuadraticParts
