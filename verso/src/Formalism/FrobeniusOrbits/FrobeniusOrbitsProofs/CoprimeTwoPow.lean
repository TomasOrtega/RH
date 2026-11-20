import Mathlib
import Formalism.FrobeniusOrbits.Statement
import Formalism.TameInertiaTowers.TowerFieldFoundations

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Group

/- English proof (translation)
Take `⟨k, rfl⟩` from `hy`. Establish `h : IsCoprime (2 : ℤ) (2 * k + 1)` using `⟨-k, 1, by ring⟩`. Conclude with `h.pow_left`.
-/
lemma coprime_two_pow (K : ℕ) {y : ℤ} (hy : Odd y) : IsCoprime ((2 : ℤ) ^ K) y := by
  obtain ⟨k, rfl⟩ := hy
  have h : IsCoprime (2 : ℤ) (2 * k + 1) := ⟨-k, 1, by ring⟩
  exact h.pow_left

/- English proof (translation)
Take `⟨m, rfl⟩` from `hx`. Take `⟨L, rfl⟩ : ∃ L, K = L + 1` from `⟨K - 1, by omega⟩`. Establish `e1 : (2 * m + 1 - 1) * (2 * m + 1 + 1) = 4 * (m * (m + 1))` using `by ring`. Establish `e2 : (2 : ℤ) ^ (L + 1 + 1) = 4 * 2 ^ L` using `by ring`. Establish `e3 : 2 * m + 1 - 1 = 2 * m` using `by ring`.

Establish `e4 : 2 * m + 1 + 1 = 2 * (m + 1)` using `by ring`. Establish `e5 : (2 : ℤ) ^ (L + 1) = 2 * 2 ^ L` using `by ring`. Rewrite using `[e1, e2, e3, e4, e5, mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0), mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0), mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Break down `Int.even_or_odd m with hm | hm` into its components or cases. Conclude with `Or.inl ((coprime_two_pow L hm.add_one).dvd_of_dvd_mul_right h)`. Conclude with `Or.inr ((coprime_two_pow L hm).dvd_of_dvd_mul_left h)`. Introduce and unpack `(h | h)`. Conclude with `h.mul_right _`.

Conclude with `h.mul_left _`.
-/
lemma key (x : ℤ) (hx : Odd x) (K : ℕ) (hK : 1 ≤ K) :
    (2 : ℤ) ^ (K + 1) ∣ (x - 1) * (x + 1) ↔ (2 : ℤ) ^ K ∣ x - 1 ∨ (2 : ℤ) ^ K ∣ x + 1 := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨L, rfl⟩ : ∃ L, K = L + 1 := ⟨K - 1, by omega⟩
  have e1 : (2 * m + 1 - 1) * (2 * m + 1 + 1) = 4 * (m * (m + 1)) := by ring
  have e2 : (2 : ℤ) ^ (L + 1 + 1) = 4 * 2 ^ L := by ring
  have e3 : 2 * m + 1 - 1 = 2 * m := by ring
  have e4 : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
  have e5 : (2 : ℤ) ^ (L + 1) = 2 * 2 ^ L := by ring
  rw [e1, e2, e3, e4, e5, mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0),
    mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0), mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)]
  constructor
  · intro h
    rcases Int.even_or_odd m with hm | hm
    · exact Or.inl ((coprime_two_pow L hm.add_one).dvd_of_dvd_mul_right h)
    · exact Or.inr ((coprime_two_pow L hm).dvd_of_dvd_mul_left h)
  · rintro (h | h)
    · exact h.mul_right _
    · exact h.mul_left _

/- English proof (translation)
Take `⟨m, rfl⟩` from `hx`. Introduce and unpack `⟨c, hc⟩`. Establish `e : (2 * m + 1) ^ 2 + 1 = 4 * (m ^ 2 + m) + 2` using `by ring`. Rewrite `hc` using `[e]`. Generalize the expression as in `m ^ 2 + m = s at hc`.

Use linear arithmetic over natural numbers and integers.
-/
lemma not_four_dvd (x : ℤ) (hx : Odd x) : ¬ (4 : ℤ) ∣ x ^ 2 + 1 := by
  obtain ⟨m, rfl⟩ := hx
  rintro ⟨c, hc⟩
  have e : (2 * m + 1) ^ 2 + 1 = 4 * (m ^ 2 + m) + 2 := by ring
  rw [e] at hc
  generalize m ^ 2 + m = s at hc
  omega

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[← ih]`. Establish `hx : Odd (l ^ (2 ^ j))` using `hl.pow`.

Establish `e : l ^ (2 ^ (j + 1)) = (l ^ (2 ^ j)) ^ 2`. Rewrite using `[show (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 from pow_succ 2 j, pow_mul]`. Establish `hK : M + (j + 1) = M + j + 1` using `by omega`. Rewrite using `[e, hK]`. Establish `h4 : ¬ (2 : ℤ) ^ (M + j + 1) ∣ (l ^ (2 ^ j)) ^ 2 + 1`.

Introduce `h`. Apply `not_four_dvd _ hx` to reduce the goal to its premises. Use `dvd_trans ?_ h` and prove the remaining obligations. Rewrite using `[show (4 : ℤ) = 2 ^ 2 by norm_num]`. Conclude with `pow_dvd_pow 2 (by omega)`.

Rewrite using `[or_iff_left h4, ← key _ hx _ (by omega)]`. Establish `e6 : (l ^ (2 ^ j)) ^ 2 - 1 = (l ^ (2 ^ j) - 1) * (l ^ (2 ^ j) + 1)` using `by ring`. Rewrite using `[e6]`.
-/
lemma ind (l : ℤ) (hl : Odd l) (M : ℕ) (hM : 1 ≤ M) (j : ℕ) :
    ((2 : ℤ) ^ (M + j) ∣ l ^ (2 ^ j) - 1 ∨ (2 : ℤ) ^ (M + j) ∣ l ^ (2 ^ j) + 1) ↔
      ((2 : ℤ) ^ M ∣ l - 1 ∨ (2 : ℤ) ^ M ∣ l + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih]
    have hx : Odd (l ^ (2 ^ j)) := hl.pow
    have e : l ^ (2 ^ (j + 1)) = (l ^ (2 ^ j)) ^ 2 := by
      rw [show (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 from pow_succ 2 j, pow_mul]
    have hK : M + (j + 1) = M + j + 1 := by omega
    rw [e, hK]
    have h4 : ¬ (2 : ℤ) ^ (M + j + 1) ∣ (l ^ (2 ^ j)) ^ 2 + 1 := by
      intro h
      apply not_four_dvd _ hx
      refine dvd_trans ?_ h
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 (by omega)
    rw [or_iff_left h4, ← key _ hx _ (by omega)]
    have e6 : (l ^ (2 ^ j)) ^ 2 - 1 = (l ^ (2 ^ j) - 1) * (l ^ (2 ^ j) + 1) := by ring
    rw [e6]

/- English proof (translation)
Establish `h` using `ZMod.intCast_eq_intCast_iff_dvd_sub 1 z m`. Rewrite `h` using `[Int.cast_one]`. Rewrite using `[← h]`. Conclude with `eq_comm`.
-/
lemma cast_eq_one (m : ℕ) (z : ℤ) : (z : ZMod m) = 1 ↔ (m : ℤ) ∣ z - 1 := by
  have h := ZMod.intCast_eq_intCast_iff_dvd_sub 1 z m
  rw [Int.cast_one] at h
  rw [← h]
  exact eq_comm

/- English proof (translation)
Establish `h` using `ZMod.intCast_eq_intCast_iff_dvd_sub (-1) z m`. Rewrite `h` using `[Int.cast_neg, Int.cast_one, sub_neg_eq_add]`. Rewrite using `[← h]`. Conclude with `eq_comm`.
-/
lemma cast_eq_neg_one (m : ℕ) (z : ℤ) : (z : ZMod m) = -1 ↔ (m : ℤ) ∣ z + 1 := by
  have h := ZMod.intCast_eq_intCast_iff_dvd_sub (-1) z m
  rw [Int.cast_neg, Int.cast_one, sub_neg_eq_add] at h
  rw [← h]
  exact eq_comm

/- English proof (translation)
Establish `hc : Nat.card (ZMod (2 ^ (e + 2)))ˣ = 2 ^ (e + 1)`. Rewrite using `[Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega), show e + 2 - 1 = e + 1 by omega]`. Simplify using the standard rewrite rules. Establish `ho : orderOf (-1 : (ZMod (2 ^ (e + 2)))ˣ) = 2`. Apply `orderOf_eq_prime` to reduce the goal to its premises.

Conclude with `neg_one_sq`. Introduce `h`. Establish `h' : ((1 : ℤ) : ZMod (2 ^ (e + 2))) = -1`. Establish `h0` using `congrArg Units.val h`. Simplify using `only [Units.val_neg, Units.val_one] at h0`.

Rewrite using `[Int.cast_one]`. Conclude with `h0.symm`. Rewrite `h'` using `[cast_eq_neg_one]`. Establish `h5` using `Int.le_of_dvd (by norm_num) h'`. Move the coercions through the operations in `at h5`.

Establish `h2 : (2 : ℤ) ^ (e + 2) = 4 * 2 ^ e` using `by ring`. Establish `h3 : (0 : ℤ) < 2 ^ e` using `by positivity`. Rewrite `h5` using `[h2]`. Generalize the expression as in `(2 : ℤ) ^ e = s at h3 h5`. Use linear arithmetic over natural numbers and integers.

Establish `h` using `Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))`. Rewrite `h` using `[Nat.card_zpowers, ho, hc]`. Unfold `HGrp`. Conclude with `Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) (h.symm.trans (pow_succ 2 e))`.
-/
lemma card_H (e : ℕ) : Nat.card (HGrp e) = 2 ^ e := by
  have hc : Nat.card (ZMod (2 ^ (e + 2)))ˣ = 2 ^ (e + 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow Nat.prime_two (by omega), show e + 2 - 1 = e + 1 by omega]
    simp
  have ho : orderOf (-1 : (ZMod (2 ^ (e + 2)))ˣ) = 2 := by
    apply orderOf_eq_prime
    · exact neg_one_sq
    · intro h
      have h' : ((1 : ℤ) : ZMod (2 ^ (e + 2))) = -1 := by
        have h0 := congrArg Units.val h
        simp only [Units.val_neg, Units.val_one] at h0
        rw [Int.cast_one]
        exact h0.symm
      rw [cast_eq_neg_one] at h'
      have h5 := Int.le_of_dvd (by norm_num) h'
      push_cast at h5
      have h2 : (2 : ℤ) ^ (e + 2) = 4 * 2 ^ e := by ring
      have h3 : (0 : ℤ) < 2 ^ e := by positivity
      rw [h2] at h5
      generalize (2 : ℤ) ^ e = s at h3 h5
      omega
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.zpowers (-1 : (ZMod (2 ^ (e + 2)))ˣ))
  rw [Nat.card_zpowers, ho, hc] at h
  unfold HGrp
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) (h.symm.trans (pow_succ 2 e))

/- English proof (translation)
Establish `hd : orderOf x ∣ 2 ^ e`. Establish `h0 : orderOf x ∣ Nat.card (HGrp e)` using `by first`. Consider the case `exact orderOf_dvd_natCard x`. Consider the case `exact orderOf_dvd_card`. Rewrite `h0` using `[card_H]`. Then use the resulting hypothesis.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨i, -, hi⟩` from `(Nat.dvd_prime_pow Nat.prime_two).1 hd`. Rewrite `h` using `[hi]`. Establish `hij : i ≤ j`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `hlt : 2 ^ j < 2 ^ i` using `by first`. Consider the case `exact Nat.pow_lt_pow_right (by norm_num) hc`. Consider the case `exact pow_lt_pow_right₀ (by norm_num) hc`.

Consider the case `exact Nat.pow_lt_pow_of_lt (by norm_num) hc`. Conclude with `absurd h (not_le.mpr hlt)`. Rewrite using `[← orderOf_dvd_iff_pow_eq_one, hi]`. Conclude with `Nat.pow_dvd_pow 2 hij`. Introduce `h`.

Conclude with `Nat.le_of_dvd (by positivity) (orderOf_dvd_of_pow_eq_one h)`.
-/
lemma order_le (e : ℕ) (x : HGrp e) (j : ℕ) : orderOf x ≤ 2 ^ j ↔ x ^ (2 ^ j) = 1 := by
  have hd : orderOf x ∣ 2 ^ e := by
    have h0 : orderOf x ∣ Nat.card (HGrp e) := by
      first
        | exact orderOf_dvd_natCard x
        | exact orderOf_dvd_card
    rwa [card_H] at h0
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    rw [hi] at h
    have hij : i ≤ j := by
      by_contra hc
      push_neg at hc
      have hlt : 2 ^ j < 2 ^ i := by
        first
          | exact Nat.pow_lt_pow_right (by norm_num) hc
          | exact pow_lt_pow_right₀ (by norm_num) hc
          | exact Nat.pow_lt_pow_of_lt (by norm_num) hc
      exact absurd h (not_le.mpr hlt)
    rw [← orderOf_dvd_iff_pow_eq_one, hi]
    exact Nat.pow_dvd_pow 2 hij
  · intro h
    exact Nat.le_of_dvd (by positivity) (orderOf_dvd_of_pow_eq_one h)

/- English proof (translation)
Establish `h0 : orderOf x ∣ Nat.card (HGrp e)` using `by first`. Consider the case `exact orderOf_dvd_natCard x`. Consider the case `exact orderOf_dvd_card`. Rewrite `h0` using `[card_H]`. Conclude with `Nat.le_of_dvd (by positivity) h0`.
-/
lemma order_le_card (e : ℕ) (x : HGrp e) : orderOf x ≤ 2 ^ e := by
  have h0 : orderOf x ∣ Nat.card (HGrp e) := by
    first
      | exact orderOf_dvd_natCard x
      | exact orderOf_dvd_card
  rw [card_H] at h0
  exact Nat.le_of_dvd (by positivity) h0

/- English proof (translation)
Unfold `hcl`. Rewrite using `[← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn⟩`. Break down `Int.even_or_odd n with h | h` into its components or cases.

Use `left`. Rewrite using `[← hn, h.neg_one_zpow]`. Use `right`. Rewrite using `[← hn, h.neg_one_zpow]`. Introduce and unpack `(h | h)`.

Conclude with `⟨0, by rw [zpow_zero, h]⟩`. Conclude with `⟨1, by rw [zpow_one, h]⟩`.
-/
lemma hcl_pow_eq_one (e : ℕ) (u : (ZMod (2 ^ (e + 2)))ˣ) (k : ℕ) :
    (hcl e u) ^ k = 1 ↔ u ^ k = 1 ∨ u ^ k = -1 := by
  unfold hcl
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    rcases Int.even_or_odd n with h | h
    · left
      rw [← hn, h.neg_one_zpow]
    · right
      rw [← hn, h.neg_one_zpow]
  · rintro (h | h)
    · exact ⟨0, by rw [zpow_zero, h]⟩
    · exact ⟨1, by rw [zpow_one, h]⟩

/- English proof (translation)
Assume the negation of the conclusion as `hl`. Rewrite `hl` using `[Int.not_odd_iff_even]`. Take `⟨c, rfl⟩` from `hl`. Establish `h1 : ((c + c : ℤ) : ZMod (2 ^ (e + 2))) * ((u⁻¹ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = 1`. Rewrite using `[← hu, Units.mul_inv]`.

Establish `h2` using `congrArg (ZMod.castHom (dvd_pow_self 2 (by omega : e + 2 ≠ 0)) (ZMod 2)) h1`. Rewrite `h2` using `[map_mul, map_one, map_intCast]`. Establish `h3 : ((c + c : ℤ) : ZMod 2) = 0` using `by first`. Consider the case `(rw [Int.cast_add, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul])`. Consider the case `(rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ⟨c, by push_cast; ring⟩)`.

Rewrite `h2` using `[h3, zero_mul]`. Conclude with `zero_ne_one h2`.
-/
lemma odd_of_unit (e : ℕ) (l : ℤ) (u : (ZMod (2 ^ (e + 2)))ˣ)
    (hu : (u : ZMod (2 ^ (e + 2))) = (l : ZMod _)) : Odd l := by
  by_contra hl
  rw [Int.not_odd_iff_even] at hl
  obtain ⟨c, rfl⟩ := hl
  have h1 : ((c + c : ℤ) : ZMod (2 ^ (e + 2))) * ((u⁻¹ : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = 1 := by
    rw [← hu, Units.mul_inv]
  have h2 := congrArg (ZMod.castHom (dvd_pow_self 2 (by omega : e + 2 ≠ 0)) (ZMod 2)) h1
  rw [map_mul, map_one, map_intCast] at h2
  have h3 : ((c + c : ℤ) : ZMod 2) = 0 := by
    first
      | (rw [Int.cast_add, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul])
      | (rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ⟨c, by push_cast; ring⟩)
  rw [h3, zero_mul] at h2
  exact zero_ne_one h2

end Group

open Formalism.FrobeniusOrbits.Group

/- English proof (translation)
Assemble the required witnesses or components as `⟨by norm_num [HostHyp], fun e => layerExists (e + 2) 11 7⟩`.
-/
theorem hostExample : HostExample :=
  ⟨by norm_num [HostHyp], fun e => layerExists (e + 2) 11 7⟩

/- English proof (translation)
Establish `hd : orderOf (hcl e (u5 (e + 2))) ∣ 2 ^ e`. Establish `h0 : orderOf (hcl e (u5 (e + 2))) ∣ Nat.card (HGrp e)` using `by first`. Consider the case `exact orderOf_dvd_natCard _`. Consider the case `exact orderOf_dvd_card`. Rewrite `h0` using `[card_H]`. Then use the resulting hypothesis.

Take `⟨i, hie, hi⟩` from `(Nat.dvd_prime_pow Nat.prime_two).1 hd`. Rewrite using `[hi]`. Break down `Nat.lt_or_ge i e with hlt | hge` into its components or cases. It suffices to derive a contradiction. Take `⟨j, rfl⟩ : ∃ j, e = j + 1` from `⟨e - 1, by omega⟩`.

Establish `hle : orderOf (hcl (j + 1) (u5 (j + 1 + 2))) ≤ 2 ^ j`. Rewrite using `[hi]`. Conclude with `Nat.pow_le_pow_right (by norm_num) (by omega)`. Rewrite `hle` using `[order_le, hcl_pow_eq_one]`. Establish `hv : ((u5 (j + 1 + 2) : (ZMod (2 ^ (j + 1 + 2)))ˣ) : ZMod (2 ^ (j + 1 + 2))) = ((5 : ℤ) : ZMod (2 ^ (j + 1 + 2)))` using `by first`.

Consider the case `(unfold u5; rw [ZMod.coe_unitOfCoprime]; norm_num)`. Consider the case `(unfold u5; simp)`. Establish `h5 : Odd (5 : ℤ)` using `⟨2, by norm_num⟩`. Establish `e3 : 3 + j = j + 1 + 2` using `by omega`. Break down `hle with h | h` into its components or cases.

Establish `h'` using `congrArg Units.val h`. Rewrite `h'` using `[Units.val_pow_eq_pow_val, hv, Units.val_one, ← Int.cast_pow, cast_eq_one]`. Move the coercions through the operations in `at h'`. Establish `h8` using `(ind 5 h5 3 (by norm_num) j).1 (Or.inl (by rw [e3]; exact h'))`. Use `first`.

Consider the case `norm_num at h8`. Consider the case `omega`. Establish `h'` using `congrArg Units.val h`. Rewrite `h'` using `[Units.val_pow_eq_pow_val, hv, Units.val_neg, Units.val_one, ← Int.cast_pow, cast_eq_neg_one]`. Move the coercions through the operations in `at h'`.

Establish `h8` using `(ind 5 h5 3 (by norm_num) j).1 (Or.inr (by rw [e3]; exact h'))`. Use `first`. Consider the case `norm_num at h8`. Consider the case `omega`. Rewrite using `[show i = e by omega]`.
-/
private lemma orderOf_hcl_u5_eq_two_pow (e : ℕ) : orderOf (hcl e (u5 (e + 2))) = 2 ^ e := by
  have hd : orderOf (hcl e (u5 (e + 2))) ∣ 2 ^ e := by
    have h0 : orderOf (hcl e (u5 (e + 2))) ∣ Nat.card (HGrp e) := by
      first
      | exact orderOf_dvd_natCard _
      | exact orderOf_dvd_card
    rwa [card_H] at h0
  obtain ⟨i, hie, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  rw [hi]
  rcases Nat.lt_or_ge i e with hlt | hge
  · exfalso
    obtain ⟨j, rfl⟩ : ∃ j, e = j + 1 := ⟨e - 1, by omega⟩
    have hle : orderOf (hcl (j + 1) (u5 (j + 1 + 2))) ≤ 2 ^ j := by
      rw [hi]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [order_le, hcl_pow_eq_one] at hle
    have hv : ((u5 (j + 1 + 2) : (ZMod (2 ^ (j + 1 + 2)))ˣ) : ZMod (2 ^ (j + 1 + 2))) =
        ((5 : ℤ) : ZMod (2 ^ (j + 1 + 2))) := by
      first
        | (unfold u5; rw [ZMod.coe_unitOfCoprime]; norm_num)
        | (unfold u5; simp)
    have h5 : Odd (5 : ℤ) := ⟨2, by norm_num⟩
    have e3 : 3 + j = j + 1 + 2 := by omega
    rcases hle with h | h
    · have h' := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val, hv, Units.val_one, ← Int.cast_pow, cast_eq_one] at h'
      push_cast at h'
      have h8 := (ind 5 h5 3 (by norm_num) j).1 (Or.inl (by rw [e3]; exact h'))
      first
        | norm_num at h8
        | omega
    · have h' := congrArg Units.val h
      rw [Units.val_pow_eq_pow_val, hv, Units.val_neg, Units.val_one, ← Int.cast_pow, cast_eq_neg_one] at h'
      push_cast at h'
      have h8 := (ind 5 h5 3 (by norm_num) j).1 (Or.inr (by rw [e3]; exact h'))
      first
        | norm_num at h8
        | omega
  · rw [show i = e by omega]

/- English proof (translation)
Unfold `HostGroup`. Introduce `e`. Establish `hne : (-1 : ℤˣ) ≠ 1` using `by first`. Consider the case `decide`. Consider the case `(intro h; have h' := congrArg Units.val h; norm_num at h')`.

Establish `hU : Nat.card ℤˣ = 2` using `by first`. Consider the case `(rw [Nat.card_eq_fintype_card]; rfl)`. Consider the case `(rw [Nat.card_eq_fintype_card]; decide)`. Consider the case `simp`. Establish `hfin : Finite (HGrp e)` using `Nat.finite_of_card_ne_zero (by rw [card_H]; positivity)`.

Establish `h5` using `orderOf_hcl_u5_eq_two_pow e`. Unfold `GG Psi cc sg chD G0 c0`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, card_H e, h5, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.card_prod, Nat.card_prod, hU, card_H]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hs : Function.Surjective ((MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.fst (ℤˣ × ℤˣ) (HGrp e)))` using `fun b => ⟨((1, b), 1), rfl⟩ first`. Consider the case `(rw [Subgroup.index_ker, Set.range_eq_univ.2 hs, Nat.card_univ, hU])`. Consider the case `(rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hs, Subgroup.card_top, hU])`. Introduce `h`. Rewrite `h` using `[MonoidHom.mem_ker]`.

Conclude with `hne h`. Rewrite using `[MonoidHom.mem_ker]`. Both sides reduce to the same expression. Apply `orderOf_eq_prime` to reduce the goal to its premises. Conclude with `Prod.ext (Prod.ext (by simp [sq]) (by simp [sq])) (by simp [sq])`.

Introduce `h`. Conclude with `hne (congrArg (fun x => x.1.1) h)`. Conclude with `isCyclic_of_orderOf_eq_card _ (by rw [h5, card_H])`. Establish `hg : hcl e (u5 (e + 2)) ^ (2 ^ e) = 1`. Rewrite using `[← h5]`.

Conclude with `pow_orderOf_eq_one _`. Set `f0 : ℤ →+ Additive (HGrp e)` to `zmultiplesHom (Additive (HGrp e)) (Additive.ofMul (hcl e (u5 (e + 2))))`. Establish `hf0 : f0 ((2 ^ e : ℕ) : ℤ) = 0` using `by show ((2 ^ e : ℕ) : ℤ) • Additive.ofMul (hcl e (u5 (e + 2))) = 0 first`. Consider the case `(rw [← ofMul_zpow, zpow_natCast, hg, ofMul_one])`. Consider the case `(rw [natCast_zsmul, ← ofMul_pow, hg, ofMul_one])`.

Consider the case `simp [← ofMul_zpow, hg]`. Set `f1 : ZMod (2 ^ e) →+ Additive (HGrp e)` to `ZMod.lift (2 ^ e) ⟨f0, hf0⟩`. Set `f : Multiplicative (ZMod (2 ^ e)) →* HGrp e` to `{ toFun := fun x => Additive.toMul (f1 (Multiplicative.toAdd x)) map_one' := by first`. Consider the case `simp`. Consider the case `rfl`.

Use the proof step `map_mul' := fun x y => by first`. Consider the case `simp`. Consider the case `(rw [toAdd_mul, map_add, toMul_add]) }`. Establish `hf1 : f (Multiplicative.ofAdd 1) = hcl e (u5 (e + 2))` using `by show Additive.toMul (f1 1) = hcl e (u5 (e + 2))`. Establish `h1 : (1 : ZMod (2 ^ e)) = ((1 : ℤ) : ZMod (2 ^ e))` using `by simp`.

Rewrite using `[h1, ZMod.lift_coe]`. Use `show Additive.toMul ((1 : ℤ) • Additive.ofMul (hcl e (u5 (e + 2)))) = hcl e (u5 (e + 2))`. Rewrite using `[one_zsmul]`. Both sides reduce to the same expression. Establish `hsurj : Function.Surjective f`.

Introduce `y`. Establish `htop : Subgroup.zpowers (hcl e (u5 (e + 2))) = ⊤` using `Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, h5, card_H])`. Establish `hy : y ∈ Subgroup.zpowers (hcl e (u5 (e + 2)))`. Rewrite using `[htop]`. Conclude with `Subgroup.mem_top y`.

Take `⟨k, hk⟩` from `Subgroup.mem_zpowers_iff.1 hy`. Use `⟨Multiplicative.ofAdd (k : ZMod (2 ^ e)), ?_⟩` and prove the remaining obligations. Use `show Additive.toMul (f1 (k : ZMod (2 ^ e))) = y`. Rewrite using `[ZMod.lift_coe]`. Use `show Additive.toMul (k • Additive.ofMul (hcl e (u5 (e + 2)))) = y`.

Rewrite using `[← hk]`. Use `first`. Consider the case `rfl`. Consider the case `simp [← ofMul_zpow]`. Establish `hbij : Function.Bijective f` using `by haveI : NeZero (2 ^ e) := ⟨by positivity⟩`.

Establish `hc : Nat.card (Multiplicative (ZMod (2 ^ e))) ≤ Nat.card (HGrp e)`. Express the relevant statement in the definitionally equal form `Nat.card (ZMod (2 ^ e)) ≤ Nat.card (HGrp e)`. Rewrite using `[Nat.card_zmod, card_H]`. Use `first`. Consider the case `exact hsurj.bijective_of_nat_card_le hc`.

Consider the case `exact (Function.Surjective.bijective_of_nat_card_le hsurj hc)`. Conclude with `⟨MulEquiv.ofBijective f hbij, hf1⟩`.
-/
theorem hostGroup : HostGroup := by
  unfold HostGroup
  intro e
  have hne : (-1 : ℤˣ) ≠ 1 := by
    first
      | decide
      | (intro h; have h' := congrArg Units.val h; norm_num at h')
  have hU : Nat.card ℤˣ = 2 := by
    first
      | (rw [Nat.card_eq_fintype_card]; rfl)
      | (rw [Nat.card_eq_fintype_card]; decide)
      | simp
  have hfin : Finite (HGrp e) := Nat.finite_of_card_ne_zero (by rw [card_H]; positivity)
  have h5 := orderOf_hcl_u5_eq_two_pow e
  unfold GG Psi cc sg chD G0 c0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, card_H e, h5, ?_⟩
  · rw [Nat.card_prod, Nat.card_prod, hU, card_H]
    ring
  · have hs : Function.Surjective ((MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.fst (ℤˣ × ℤˣ) (HGrp e))) :=
      fun b => ⟨((1, b), 1), rfl⟩
    first
      | (rw [Subgroup.index_ker, Set.range_eq_univ.2 hs, Nat.card_univ, hU])
      | (rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hs, Subgroup.card_top, hU])
  · intro h
    rw [MonoidHom.mem_ker] at h
    exact hne h
  · rw [MonoidHom.mem_ker]
    rfl
  · apply orderOf_eq_prime
    · exact Prod.ext (Prod.ext (by simp [sq]) (by simp [sq])) (by simp [sq])
    · intro h
      exact hne (congrArg (fun x => x.1.1) h)
  · exact isCyclic_of_orderOf_eq_card _ (by rw [h5, card_H])
  · have hg : hcl e (u5 (e + 2)) ^ (2 ^ e) = 1 := by
      rw [← h5]
      exact pow_orderOf_eq_one _
    let f0 : ℤ →+ Additive (HGrp e) := zmultiplesHom (Additive (HGrp e)) (Additive.ofMul (hcl e (u5 (e + 2))))
    have hf0 : f0 ((2 ^ e : ℕ) : ℤ) = 0 := by
      show ((2 ^ e : ℕ) : ℤ) • Additive.ofMul (hcl e (u5 (e + 2))) = 0
      first
        | (rw [← ofMul_zpow, zpow_natCast, hg, ofMul_one])
        | (rw [natCast_zsmul, ← ofMul_pow, hg, ofMul_one])
        | simp [← ofMul_zpow, hg]
    let f1 : ZMod (2 ^ e) →+ Additive (HGrp e) := ZMod.lift (2 ^ e) ⟨f0, hf0⟩
    let f : Multiplicative (ZMod (2 ^ e)) →* HGrp e :=
      { toFun := fun x => Additive.toMul (f1 (Multiplicative.toAdd x))
        map_one' := by
          first
            | simp
            | rfl
        map_mul' := fun x y => by
          first
            | simp
            | (rw [toAdd_mul, map_add, toMul_add]) }
    have hf1 : f (Multiplicative.ofAdd 1) = hcl e (u5 (e + 2)) := by
      show Additive.toMul (f1 1) = hcl e (u5 (e + 2))
      have h1 : (1 : ZMod (2 ^ e)) = ((1 : ℤ) : ZMod (2 ^ e)) := by simp
      rw [h1, ZMod.lift_coe]
      show Additive.toMul ((1 : ℤ) • Additive.ofMul (hcl e (u5 (e + 2)))) = hcl e (u5 (e + 2))
      rw [one_zsmul]
      rfl
    have hsurj : Function.Surjective f := by
      intro y
      have htop : Subgroup.zpowers (hcl e (u5 (e + 2))) = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, h5, card_H])
      have hy : y ∈ Subgroup.zpowers (hcl e (u5 (e + 2))) := by
        rw [htop]
        exact Subgroup.mem_top y
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
      refine ⟨Multiplicative.ofAdd (k : ZMod (2 ^ e)), ?_⟩
      show Additive.toMul (f1 (k : ZMod (2 ^ e))) = y
      rw [ZMod.lift_coe]
      show Additive.toMul (k • Additive.ofMul (hcl e (u5 (e + 2)))) = y
      rw [← hk]
      first
        | rfl
        | simp [← ofMul_zpow]
    have hbij : Function.Bijective f := by
      haveI : NeZero (2 ^ e) := ⟨by positivity⟩
      have hc : Nat.card (Multiplicative (ZMod (2 ^ e))) ≤ Nat.card (HGrp e) := by
        change Nat.card (ZMod (2 ^ e)) ≤ Nat.card (HGrp e)
        rw [Nat.card_zmod, card_H]
      first
        | exact hsurj.bijective_of_nat_card_le hc
        | exact (Function.Surjective.bijective_of_nat_card_le hsurj hc)
    exact ⟨MulEquiv.ofBijective f hbij, hf1⟩

/- English proof (translation)
Unfold `HostOrders`. Introduce `e`. Use `⟨fun j l u hu => ?_, ?_⟩` and prove the remaining obligations. Establish `hl : Odd l` using `odd_of_unit e l u hu`. Establish `h1 : u ^ (2 ^ j) = 1 ↔ ((l ^ (2 ^ j) : ℤ) : ZMod (2 ^ (e + 2))) = 1`.

Rewrite using `[Units.ext_iff, Units.val_pow_eq_pow_val, hu, Units.val_one, Int.cast_pow]`. Establish `h2 : u ^ (2 ^ j) = -1 ↔ ((l ^ (2 ^ j) : ℤ) : ZMod (2 ^ (e + 2))) = -1`. Rewrite using `[Units.ext_iff, Units.val_pow_eq_pow_val, hu, Units.val_neg, Units.val_one, Int.cast_pow]`. Break down `Nat.lt_or_ge (e + 1) j with hj | hj` into its components or cases. Simplify using `only [cast_eq_one, cast_eq_neg_one]`.

Rewrite using `[show e + 2 - j = 0 by omega]`. Simplify using `only [pow_zero, Nat.cast_one, one_dvd, or_self, iff_true]`. Conclude with `(order_le_card e _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))`. Rewrite using `[order_le, hcl_pow_eq_one, h1, h2]`. Simplify using `only [cast_eq_one, cast_eq_neg_one]`.

Use `push_cast`. Take `⟨M, hM⟩ : ∃ M, e + 2 = M + j` from `⟨e + 2 - j, by omega⟩`. Rewrite using `[hM, show M + j - j = M by omega]`. Conclude with `ind l hl M (by omega) j`. Unfold `GG cc G0 c0`.

Establish `hne : (-1 : ℤˣ) ≠ 1` using `by first`. Consider the case `decide`. Consider the case `(intro h; have h' := congrArg Units.val h; norm_num at h')`. Introduce `g`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[Subgroup.mem_zpowers_iff]`. Introduce and unpack `⟨k, hk⟩`. Establish `hk1 : g.1.1 ^ k = -1` using `congrArg (fun x => x.1.1) hk`. Establish `hk2 : g.1.2 ^ k = -1` using `congrArg (fun x => x.1.2) hk`. Establish `hk3 : g.2 ^ k = 1` using `congrArg (fun x => x.2) hk`.

Establish `hodd : Odd k`. Break down `Int.even_or_odd k with he | ho` into its components or cases. It suffices to derive a contradiction. Break down `Int.units_eq_one_or g.1.1 with h1 | h1` into its components or cases. Rewrite `hk1` using `[h1, one_zpow]`.

Conclude with `hne hk1.symm`. Rewrite `hk1` using `[h1, he.neg_one_zpow]`. Conclude with `hne hk1.symm`. Conclude with `ho`. Establish `hu : ∀ v : ℤˣ, v ^ k = -1 → v = -1`.

Introduce `v hv`. Break down `Int.units_eq_one_or v with h1 | h1` into its components or cases. Rewrite `hv` using `[h1, one_zpow]`. Conclude with `absurd hv.symm hne`. Conclude with `h1`.

Establish `hg2 : g.2 = 1`. Establish `hd : (orderOf g.2 : ℤ) ∣ k` using `orderOf_dvd_iff_zpow_eq_one.2 hk3`. Establish `hd2 : orderOf g.2 ∣ 2 ^ e`. Establish `h0 : orderOf g.2 ∣ Nat.card (HGrp e)` using `by first`. Consider the case `exact orderOf_dvd_natCard _`.

Consider the case `exact orderOf_dvd_card`. Rewrite `h0` using `[card_H]`. Then use the resulting hypothesis. Take `⟨i, -, hi⟩` from `(Nat.dvd_prime_pow Nat.prime_two).1 hd2`. Establish `hi0 : i = 0`. Assume the negation of the conclusion as `hne0`.

Take `⟨i', rfl⟩ : ∃ i', i = i' + 1` from `⟨i - 1, by omega⟩`. Rewrite `hd` using `[hi, pow_succ]`. Move the coercions through the operations in `at hd`. Establish `h2k : (2 : ℤ) ∣ k` using `dvd_trans (Dvd.intro_left _ rfl) hd`. Conclude with `(Int.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2k)`.

Rewrite `hi` using `[hi0, pow_zero, orderOf_eq_one_iff]`. Conclude with `hi`. Conclude with `Prod.ext (Prod.ext (hu _ hk1) (hu _ hk2)) hg2`. Introduce and unpack `rfl`. Conclude with `Subgroup.mem_zpowers _`.
-/
theorem hostOrders : HostOrders := by
  unfold HostOrders
  intro e
  refine ⟨fun j l u hu => ?_, ?_⟩
  · have hl : Odd l := odd_of_unit e l u hu
    have h1 : u ^ (2 ^ j) = 1 ↔ ((l ^ (2 ^ j) : ℤ) : ZMod (2 ^ (e + 2))) = 1 := by
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, hu, Units.val_one, Int.cast_pow]
    have h2 : u ^ (2 ^ j) = -1 ↔ ((l ^ (2 ^ j) : ℤ) : ZMod (2 ^ (e + 2))) = -1 := by
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, hu, Units.val_neg, Units.val_one, Int.cast_pow]
    rcases Nat.lt_or_ge (e + 1) j with hj | hj
    · simp only [cast_eq_one, cast_eq_neg_one]
      rw [show e + 2 - j = 0 by omega]
      simp only [pow_zero, Nat.cast_one, one_dvd, or_self, iff_true]
      exact (order_le_card e _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    · rw [order_le, hcl_pow_eq_one, h1, h2]
      simp only [cast_eq_one, cast_eq_neg_one]
      push_cast
      obtain ⟨M, hM⟩ : ∃ M, e + 2 = M + j := ⟨e + 2 - j, by omega⟩
      rw [hM, show M + j - j = M by omega]
      exact ind l hl M (by omega) j
  · unfold GG cc G0 c0
    have hne : (-1 : ℤˣ) ≠ 1 := by
      first
        | decide
        | (intro h; have h' := congrArg Units.val h; norm_num at h')
    intro g
    constructor
    · rw [Subgroup.mem_zpowers_iff]
      rintro ⟨k, hk⟩
      have hk1 : g.1.1 ^ k = -1 := congrArg (fun x => x.1.1) hk
      have hk2 : g.1.2 ^ k = -1 := congrArg (fun x => x.1.2) hk
      have hk3 : g.2 ^ k = 1 := congrArg (fun x => x.2) hk
      have hodd : Odd k := by
        rcases Int.even_or_odd k with he | ho
        · exfalso
          rcases Int.units_eq_one_or g.1.1 with h1 | h1
          · rw [h1, one_zpow] at hk1
            exact hne hk1.symm
          · rw [h1, he.neg_one_zpow] at hk1
            exact hne hk1.symm
        · exact ho
      have hu : ∀ v : ℤˣ, v ^ k = -1 → v = -1 := by
        intro v hv
        rcases Int.units_eq_one_or v with h1 | h1
        · rw [h1, one_zpow] at hv
          exact absurd hv.symm hne
        · exact h1
      have hg2 : g.2 = 1 := by
        have hd : (orderOf g.2 : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.2 hk3
        have hd2 : orderOf g.2 ∣ 2 ^ e := by
          have h0 : orderOf g.2 ∣ Nat.card (HGrp e) := by
            first
              | exact orderOf_dvd_natCard _
              | exact orderOf_dvd_card
          rwa [card_H] at h0
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
        have hi0 : i = 0 := by
          by_contra hne0
          obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          rw [hi, pow_succ] at hd
          push_cast at hd
          have h2k : (2 : ℤ) ∣ k := dvd_trans (Dvd.intro_left _ rfl) hd
          exact (Int.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2k)
        rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
        exact hi
      exact Prod.ext (Prod.ext (hu _ hk1) (hu _ hk2)) hg2
    · rintro rfl
      exact Subgroup.mem_zpowers _

/- English proof (translation)
Unfold `HostRecip`. Introduce `q d h`. Unfold `HostHyp at h`. Take `⟨-, -, hq8, hd16, hj⟩` from `h`. Establish `hq4 : q % 4 = 3` using `by omega`.

Establish `hd4 : d % 4 = 3` using `by omega`. Establish `hqo : Odd q` using `Nat.odd_iff.2 (by omega)`. Establish `hdo : Odd d` using `Nat.odd_iff.2 (by omega)`. Establish `hχq : ZMod.χ₄ (q : ZMod 4) = -1` using `ZMod.χ₄_nat_three_mod_four hq4`. Establish `hχd : ZMod.χ₄ (d : ZMod 4) = -1` using `ZMod.χ₄_nat_three_mod_four hd4`.

Rewrite `hj` using `[jacobiSym.neg _ hqo, hχq]`. Rewrite using `[jacobiSym.neg _ hdo, hχd, jacobiSym.quadratic_reciprocity_three_mod_four hq4 hd4]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hostRecip : HostRecip := by
  unfold HostRecip
  intro q d h
  unfold HostHyp at h
  obtain ⟨-, -, hq8, hd16, hj⟩ := h
  have hq4 : q % 4 = 3 := by omega
  have hd4 : d % 4 = 3 := by omega
  have hqo : Odd q := Nat.odd_iff.2 (by omega)
  have hdo : Odd d := Nat.odd_iff.2 (by omega)
  have hχq : ZMod.χ₄ (q : ZMod 4) = -1 := ZMod.χ₄_nat_three_mod_four hq4
  have hχd : ZMod.χ₄ (d : ZMod 4) = -1 := ZMod.χ₄_nat_three_mod_four hd4
  rw [jacobiSym.neg _ hqo, hχq] at hj
  rw [jacobiSym.neg _ hdo, hχd, jacobiSym.quadratic_reciprocity_three_mod_four hq4 hd4]
  linarith

end Formalism.FrobeniusOrbits
