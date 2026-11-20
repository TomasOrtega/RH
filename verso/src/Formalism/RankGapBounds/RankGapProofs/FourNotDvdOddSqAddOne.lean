import Formalism.RankGapBounds.RandomSubsetCounterexample

namespace Formalism.RankGapBounds.LocalQuadraticParts

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]`.
-/
lemma zmod_int_eq_one_iff (n : ℕ) (x : ℤ) : ((x : ZMod n) = 1) ↔ (n : ℤ) ∣ x - 1 := by
  rw [← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]

/- English proof (translation)
Rewrite using `[← sub_eq_zero, sub_neg_eq_add, ← Int.cast_one, ← Int.cast_add, ZMod.intCast_zmod_eq_zero_iff_dvd]`.
-/
lemma zmod_int_eq_neg_one_iff (n : ℕ) (x : ℤ) : ((x : ZMod n) = -1) ↔ (n : ℤ) ∣ x + 1 := by
  rw [← sub_eq_zero, sub_neg_eq_add, ← Int.cast_one, ← Int.cast_add, ZMod.intCast_zmod_eq_zero_iff_dvd]

/- English proof (translation)
Establish `h` using `zmod_int_eq_one_iff n (l : ℤ)`. Simplify using `using h`.
-/
lemma zmod_nat_eq_one_iff (n l : ℕ) : ((l : ZMod n) = 1) ↔ (n : ℤ) ∣ (l : ℤ) - 1 := by
  have h := zmod_int_eq_one_iff n (l : ℤ)
  simpa using h

/- English proof (translation)
Establish `h` using `zmod_int_eq_neg_one_iff n (l : ℤ)`. Simplify using `using h`.
-/
lemma zmod_nat_eq_neg_one_iff (n l : ℕ) : ((l : ZMod n) = -1) ↔ (n : ℤ) ∣ (l : ℤ) + 1 := by
  have h := zmod_int_eq_neg_one_iff n (l : ℤ)
  simpa using h

/- English proof (translation)
Take `⟨k, rfl⟩` from `hy`. Establish `h : (2 * k + 1) ^ 2 + 1 = 4 * (k ^ 2 + k) + 2` using `by ring`. Rewrite using `[h]`. Generalize the expression as in `k ^ 2 + k = t`. Use linear arithmetic over natural numbers and integers.
-/
lemma four_not_dvd_odd_sq_add_one (y : ℤ) (hy : Odd y) : ¬ (4 : ℤ) ∣ y ^ 2 + 1 := by
  obtain ⟨k, rfl⟩ := hy
  have h : (2 * k + 1) ^ 2 + 1 = 4 * (k ^ 2 + k) + 2 := by ring
  rw [h]
  generalize k ^ 2 + k = t
  omega

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, m = n + 1` from `⟨m - 1, by omega⟩`. Take `⟨k, rfl⟩` from `hx`. Establish `e1 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1))` using `by ring`. Establish `e2 : 2 * k + 1 - 1 = 2 * k` using `by ring`. Establish `e3 : 2 * k + 1 + 1 = 2 * (k + 1)` using `by ring`.

Establish `p1 : (2 : ℤ) ^ (n + 1 + 1) = 4 * 2 ^ n` using `by ring`. Establish `p2 : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n` using `by ring`. Rewrite using `[e1, e2, e3, p1, p2, mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0), mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0), mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Break down `Int.even_or_odd k with ⟨b, hb⟩ | ⟨b, hb⟩` into its components or cases. Use `left`. Establish `hc : IsCoprime ((2 : ℤ) ^ n) (k + 1)`. Apply `IsCoprime.pow_left` to reduce the goal to its premises. Use `⟨-b, 1, ?_⟩` and prove the remaining obligations.

Rewrite using `[hb]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `hc.dvd_of_dvd_mul_right h`. Use `right`. Establish `hc : IsCoprime ((2 : ℤ) ^ n) k`.

Apply `IsCoprime.pow_left` to reduce the goal to its premises. Use `⟨-b, 1, ?_⟩` and prove the remaining obligations. Rewrite using `[hb]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `hc.dvd_of_dvd_mul_left h`.

Introduce and unpack `(h | h)`. Conclude with `dvd_mul_of_dvd_left h _`. Conclude with `dvd_mul_of_dvd_right h _`.
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

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => intro x _ m _`. Simplify using the standard rewrite rules. Consider the case `succ j ih`. Introduce `x hx m hm`.

Establish `hy : Odd (x ^ (2 ^ j))` using `hx.pow`. Establish `hpow : x ^ (2 ^ (j + 1)) = (x ^ (2 ^ j)) ^ 2` using `by rw [pow_succ, pow_mul]`. Establish `hnot : ¬ (2 : ℤ) ^ (m + (j + 1)) ∣ (x ^ (2 ^ j)) ^ 2 + 1`. Introduce `h`. Apply `four_not_dvd_odd_sq_add_one _ hy` to reduce the goal to its premises.

Use `dvd_trans ?_ h` and prove the remaining obligations. Establish `: (4 : ℤ) = 2 ^ 2` using `by norm_num`. Rewrite using `[this]`. Conclude with `pow_dvd_pow 2 (by omega)`. Rewrite using `[hpow, ← ih x hx m hm, show m + (j + 1) = m + j + 1 by omega, ← sq_sub_one_dvd_iff _ hy (m + j) (by omega)]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `(h | h)`. Conclude with `h`. Conclude with `absurd h (by rw [show m + j + 1 = m + (j + 1) by omega]; exact hnot)`. Introduce `h`.

Conclude with `Or.inl h`.
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

/- English proof (translation)
Establish `h` using `pow_two_pow_pm_iff j x hx (e + 2 - j) (by omega)`. Rewrite `h` using `[show e + 2 - j + j = e + 2 by omega]`. Conclude with `h`.
-/
lemma pm_iff (e j : ℕ) (hj : j ≤ e) (x : ℤ) (hx : Odd x) :
    (((2 : ℤ) ^ (e + 2) ∣ x ^ (2 ^ j) - 1 ∨ (2 : ℤ) ^ (e + 2) ∣ x ^ (2 ^ j) + 1) ↔
      ((2 : ℤ) ^ (e + 2 - j) ∣ x - 1 ∨ (2 : ℤ) ^ (e + 2 - j) ∣ x + 1)) := by
  have h := pow_two_pow_pm_iff j x hx (e + 2 - j) (by omega)
  rw [show e + 2 - j + j = e + 2 by omega] at h
  exact h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, rfl⟩`. Break down `Int.even_or_odd k with h | h` into its components or cases. Conclude with `Or.inl h.neg_one_zpow`. Conclude with `Or.inr h.neg_one_zpow`.

Introduce and unpack `(rfl | rfl)`. Conclude with `⟨0, zpow_zero _⟩`. Conclude with `⟨1, zpow_one _⟩`.
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

/- English proof (translation)
Unfold `hOf`. Rewrite using `[← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff, units_zpow_neg_one_iff]`. Establish `hv : ((ZMod.unitOfCoprime l hl ^ (2 ^ j) : (ZMod (4 * 2 ^ e))ˣ) : ZMod (4 * 2 ^ e)) = (((l : ℤ) ^ (2 ^ j) : ℤ) : ZMod (4 * 2 ^ e))`. Simplify using `[Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `(h | h)`. Use `left`. Rewrite using `[← hv, h, Units.val_one]`. Use `right`. Rewrite using `[← hv, h, Units.val_neg, Units.val_one]`.

Introduce and unpack `(h | h)`. Use `left`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hv, h, Units.val_one]`. Use `right`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hv, h, Units.val_neg, Units.val_one]`.
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

/- English proof (translation)
Establish `h2 : ¬ 2 ∣ l` using `fun h => by`. Use `Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h hl) (dvd_mul_of_dvd_left (by norm_num) _)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `Int.odd_iff.mpr (by omega)`.
-/
lemma odd_of_coprime (e l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) : Odd (l : ℤ) := by
  have h2 : ¬ 2 ∣ l := fun h => by
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h hl)
      (dvd_mul_of_dvd_left (by norm_num) _)
    omega
  exact Int.odd_iff.mpr (by omega)

/- English proof (translation)
Introduce `e j l hl hj`. Rewrite using `[hOf_pow_eq_one_iff, zmod_int_eq_one_iff, zmod_int_eq_neg_one_iff, zmod_nat_eq_one_iff, zmod_nat_eq_neg_one_iff]`. Use `push_cast`. Rewrite using `[show (4 : ℤ) * 2 ^ e = 2 ^ (e + 2) by ring]`. Conclude with `pm_iff e j hj l (odd_of_coprime e l hl)`.
-/
theorem powTwoPowEqOneIff_holds : OrdersIff := by
  intro e j l hl hj
  rw [hOf_pow_eq_one_iff, zmod_int_eq_one_iff, zmod_int_eq_neg_one_iff, zmod_nat_eq_one_iff,
    zmod_nat_eq_neg_one_iff]
  push_cast
  rw [show (4 : ℤ) * 2 ^ e = 2 ^ (e + 2) by ring]
  exact pm_iff e j hj l (odd_of_coprime e l hl)

/- English proof (translation)
Introduce `e J l hl hJ hl1 hord`. Establish `hodd` using `odd_of_coprime e l hl`. Establish `hE : (hOf e l hl) ^ (2 ^ e) = 1`. Rewrite using `[powTwoPowEqOneIff_holds e e l hl le_rfl, show e + 2 - e = 2 by omega, zmod_nat_eq_one_iff, zmod_nat_eq_neg_one_iff]`. Take `⟨k, hk⟩` from `hodd`.

Use `push_cast`. Break down `Int.even_or_odd k with ⟨b, hb⟩ | ⟨b, hb⟩` into its components or cases. Use `left`. Rewrite using `[hk, hb]`. Conclude with `⟨b, by ring⟩`.

Use `right`. Rewrite using `[hk, hb]`. Conclude with `⟨b + 1, by ring⟩`. Take `⟨k, hk, hko⟩` from `(Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hE)`. Establish `hk1 : (hOf e l hl) ^ (2 ^ k) = 1`.

Rewrite using `[← hko]`. Conclude with `pow_orderOf_eq_one _`. Establish `hres` using `(powTwoPowEqOneIff_holds e k l hl hk).mp hk1`. Rewrite `hres` using `[zmod_nat_eq_one_iff, zmod_nat_eq_neg_one_iff]`. Establish `hM : ((2 : ℤ) ^ (e + 2 - k)) ≤ (l : ℤ) + 1`.

Break down `hres with h | h` into its components or cases. Move the coercions through the operations in `at h`. Establish `hpos : (0 : ℤ) < l - 1` using `by omega`. Use `Int.le_of_dvd hpos h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Move the coercions through the operations in `at h`. Establish `hpos : (0 : ℤ) < l + 1` using `by omega`. Use `Int.le_of_dvd hpos h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hJn : 2 ^ k ≤ J` using `hko ▸ hord`.

Establish `hJ' : (2 : ℝ) ^ k ≤ J` using `by exact_mod_cast hJn`. Establish `key : (4 * 2 ^ e : ℝ) = 2 ^ (e + 2 - k) * 2 ^ k`. Rewrite using `[← pow_add, show e + 2 - k + k = e + 2 by omega]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : (4 * 2 ^ e : ℝ) / J ≤ 4 * 2 ^ e / 2 ^ k` using `div_le_div_of_nonneg_left (by positivity) (by positivity) hJ'`.

Establish `h2 : (4 * 2 ^ e : ℝ) / 2 ^ k = 2 ^ (e + 2 - k)`. Rewrite using `[key]`. Clear the denominators using the available nonvanishing facts. Establish `h3 : (2 : ℝ) ^ (e + 2 - k) ≤ l + 1` using `by exact_mod_cast hM`. Combine the linear equalities and inequalities to obtain the conclusion.
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
