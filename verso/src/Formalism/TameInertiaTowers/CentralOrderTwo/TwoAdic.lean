import Mathlib
import Formalism.TameInertiaTowers.StatementGroup

namespace Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation

/- English proof (translation)
Use `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`. Rewrite using `[show padicValInt 2 z = padicValNat 2 z.natAbs from rfl, padicValNat_eq_emultiplicity (Int.natAbs_ne_zero.mpr hz), Int.emultiplicity_natAbs]`. Both sides reduce to the same expression.
-/
lemma vEq (z : ℤ) (hz : z ≠ 0) : (padicValInt 2 z : ℕ∞) = emultiplicity (2 : ℤ) z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show padicValInt 2 z = padicValNat 2 z.natAbs from rfl,
    padicValNat_eq_emultiplicity (Int.natAbs_ne_zero.mpr hz), Int.emultiplicity_natAbs]
  rfl

/- English proof (translation)
Use `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`. Rewrite using `[padicValNat_eq_emultiplicity he, ← Int.natCast_emultiplicity]`. Both sides reduce to the same expression.
-/
lemma vNat (e : ℕ) (he : e ≠ 0) : (padicValNat 2 e : ℕ∞) = emultiplicity (2 : ℤ) (e : ℤ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat_eq_emultiplicity he, ← Int.natCast_emultiplicity]
  rfl

/- English proof (translation)
Introduce `h`. Apply `ha2` to reduce the goal to its premises. Establish `h1 : |a| ^ e = 1` using `by rw [pow_abs, sub_eq_zero.mp h, abs_one]`. Establish `h2 : |a| = 1` using `(pow_eq_one_iff_of_nonneg (abs_nonneg a) he.ne').mp h1`. Rewrite using `[← sq_abs, h2, one_pow]`.
-/
lemma pow_sub_one_ne (a : ℤ) (ha2 : a ^ 2 ≠ 1) (e : ℕ) (he : 0 < e) : a ^ e - 1 ≠ 0 := by
  intro h
  apply ha2
  have h1 : |a| ^ e = 1 := by rw [pow_abs, sub_eq_zero.mp h, abs_one]
  have h2 : |a| = 1 := (pow_eq_one_iff_of_nonneg (abs_nonneg a) he.ne').mp h1
  rw [← sq_abs, h2, one_pow]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `hp : ¬ Even (a ^ n)` using `Int.not_even_iff_odd.mpr (ha.pow)`. Rewrite using `[Finset.sum_range_succ, Int.odd_add, ih]`.

Simplify using `[hp, Nat.odd_add_one]`.
-/
lemma geom_odd (a : ℤ) (ha : Odd a) (n : ℕ) : (Odd (∑ i ∈ Finset.range n, a ^ i) ↔ Odd n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : ¬ Even (a ^ n) := Int.not_even_iff_odd.mpr (ha.pow)
    rw [Finset.sum_range_succ, Int.odd_add, ih]
    simp [hp, Nat.odd_add_one]

/- English proof (translation)
Establish `h1 : a - 1 ≠ 0`. Introduce `h`. Apply `ha2` to reduce the goal to its premises. Rewrite using `[sub_eq_zero.mp h]`. Evaluate the numerical expressions.

Establish `h2 : a + 1 ≠ 0`. Introduce `h; apply ha2; rw [show a = -1 by linarith]; norm_num`. Use `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`. Rewrite using `[show a ^ 2 - 1 = (a - 1) * (a + 1) by ring, padicValInt.mul h1 h2]`.
-/
lemma sq_split (a : ℤ) (ha2 : a ^ 2 ≠ 1) :
    padicValInt 2 (a ^ 2 - 1) = padicValInt 2 (a - 1) + padicValInt 2 (a + 1) := by
  have h1 : a - 1 ≠ 0 := by
    intro h; apply ha2; rw [sub_eq_zero.mp h]; norm_num
  have h2 : a + 1 ≠ 0 := by
    intro h; apply ha2; rw [show a = -1 by linarith]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show a ^ 2 - 1 = (a - 1) * (a + 1) by ring, padicValInt.mul h1 h2]

/- English proof (translation)
Use `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`. Establish `hne` using `pow_sub_one_ne a ha2 e he`. Establish `h1 : a - 1 ≠ 0`. Introduce `h`. Apply `ha2` to reduce the goal to its premises.

Rewrite using `[sub_eq_zero.mp h]`. Evaluate the numerical expressions. Establish `h2 : a + 1 ≠ 0`. Introduce `h; apply ha2; rw [show a = -1 by linarith]; norm_num`. Establish `hdiv : (2 : ℤ) ∣ a - 1`.

Take `⟨k, rfl⟩` from `ha; exact ⟨k, by ring⟩`. Establish `hnd : ¬ (2 : ℤ) ∣ a`. Rewrite using `[← even_iff_two_dvd]`. Conclude with `Int.not_even_iff_odd.mpr ha`. Establish `key` using `Int.two_pow_sub_pow (y := 1) (n := e) hdiv hnd hev`.

Rewrite `key` using `[one_pow, ← vEq _ hne, ← vEq _ h2, ← vEq _ h1, ← vNat _ he.ne']`. Rewrite using `[sq_split a ha2]`. Normalize the coercions in `at key`. Use linear arithmetic over natural numbers and integers.
-/
lemma val_even (a : ℤ) (ha : Odd a) (ha2 : a ^ 2 ≠ 1) (e : ℕ) (he : 0 < e) (hev : Even e) :
    padicValInt 2 (a ^ e - 1) + 1 = padicValInt 2 (a ^ 2 - 1) + padicValNat 2 e := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne := pow_sub_one_ne a ha2 e he
  have h1 : a - 1 ≠ 0 := by
    intro h; apply ha2; rw [sub_eq_zero.mp h]; norm_num
  have h2 : a + 1 ≠ 0 := by
    intro h; apply ha2; rw [show a = -1 by linarith]; norm_num
  have hdiv : (2 : ℤ) ∣ a - 1 := by
    obtain ⟨k, rfl⟩ := ha; exact ⟨k, by ring⟩
  have hnd : ¬ (2 : ℤ) ∣ a := by
    rw [← even_iff_two_dvd]; exact Int.not_even_iff_odd.mpr ha
  have key := Int.two_pow_sub_pow (y := 1) (n := e) hdiv hnd hev
  rw [one_pow, ← vEq _ hne, ← vEq _ h2, ← vEq _ h1, ← vNat _ he.ne'] at key
  rw [sq_split a ha2]
  norm_cast at key
  omega

/- English proof (translation)
Use `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`. Establish `h1 : a - 1 ≠ 0`. Introduce `h`. Apply `ha2` to reduce the goal to its premises. Rewrite using `[sub_eq_zero.mp h]`.

Evaluate the numerical expressions. Establish `hs : Odd (∑ i ∈ Finset.range e, a ^ i)` using `(geom_odd a ha e).mpr hod`. Establish `hs0 : (∑ i ∈ Finset.range e, a ^ i) ≠ 0` using `fun h => by`. Rewrite using `[h] at hs; exact Int.not_even_iff_odd.mpr hs ⟨0, by norm_num⟩`. Establish `hnd : ¬ ((2 : ℕ) : ℤ) ∣ ∑ i ∈ Finset.range e, a ^ i`.

Introduce `hd`. Conclude with `Int.not_even_iff_odd.mpr hs (even_iff_two_dvd.mpr (by exact_mod_cast hd))`. Rewrite using `[← mul_geom_sum, padicValInt.mul h1 hs0, padicValInt.eq_zero_of_not_dvd hnd, add_zero]`.
-/
lemma val_odd (a : ℤ) (ha : Odd a) (ha2 : a ^ 2 ≠ 1) (e : ℕ) (hod : Odd e) :
    padicValInt 2 (a ^ e - 1) = padicValInt 2 (a - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : a - 1 ≠ 0 := by
    intro h; apply ha2; rw [sub_eq_zero.mp h]; norm_num
  have hs : Odd (∑ i ∈ Finset.range e, a ^ i) := (geom_odd a ha e).mpr hod
  have hs0 : (∑ i ∈ Finset.range e, a ^ i) ≠ 0 := fun h => by
    rw [h] at hs; exact Int.not_even_iff_odd.mpr hs ⟨0, by norm_num⟩
  have hnd : ¬ ((2 : ℕ) : ℤ) ∣ ∑ i ∈ Finset.range e, a ^ i := by
    intro hd
    exact Int.not_even_iff_odd.mpr hs (even_iff_two_dvd.mpr (by exact_mod_cast hd))
  rw [← mul_geom_sum, padicValInt.mul h1 hs0, padicValInt.eq_zero_of_not_dvd hnd, add_zero]

/- English proof (translation)
Use `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`. Establish `h0 : ((a : ZMod (2 ^ N)) ^ m = 1) ↔ (((a ^ m - 1 : ℤ)) : ZMod (2 ^ N)) = 0` using `by push_cast; exact sub_eq_zero.symm`. Rewrite using `[h0, ZMod.intCast_zmod_eq_zero_iff_dvd]`. Establish `h2` using `padicValInt_dvd_iff (p := 2) N (a ^ m - 1)`. Move the coercions through the operations in `at h2 ⊢`.

Rewrite using `[h2, or_iff_right hz]`.
-/
lemma powEq (N m : ℕ) (a : ℤ) (hz : a ^ m - 1 ≠ 0) :
    (a : ZMod (2 ^ N)) ^ m = 1 ↔ N ≤ padicValInt 2 (a ^ m - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h0 : ((a : ZMod (2 ^ N)) ^ m = 1) ↔ (((a ^ m - 1 : ℤ)) : ZMod (2 ^ N)) = 0 := by
    push_cast; exact sub_eq_zero.symm
  rw [h0, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h2 := padicValInt_dvd_iff (p := 2) N (a ^ m - 1)
  push_cast at h2 ⊢
  rw [h2, or_iff_right hz]

end Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation

namespace Formalism.TwoAdicCyclotomicDecomposition

open TwoAdicValuation in
/- English proof (translation)
Introduce `a ha ha2 e he`. Distinguish the cases in `hev : Even e`. Establish `h` using `val_even a ha ha2 e he hev`. Establish `hl : padicValNat 2 e ≤ Nat.log 2 e` using `padicValNat_le_nat_log e`. Rewrite using `[if_pos hev]`.

Apply the tactic sequence `constructor <;> omega`. Establish `hod : Odd e` using `Nat.not_even_iff_odd.mp hev`. Establish `h` using `val_odd a ha ha2 e hod`. Establish `hs` using `sq_split a ha2`. Rewrite using `[if_neg hev]`.

Apply the tactic sequence `constructor <;> omega`.
-/
theorem twoAdicVal : TwoAdicVal := by
  intro a ha ha2 e he
  by_cases hev : Even e
  · have h := val_even a ha ha2 e he hev
    have hl : padicValNat 2 e ≤ Nat.log 2 e := padicValNat_le_nat_log e
    rw [if_pos hev]
    constructor <;> omega
  · have hod : Odd e := Nat.not_even_iff_odd.mp hev
    have h := val_odd a ha ha2 e hod
    have hs := sq_split a ha2
    rw [if_neg hev]
    constructor <;> omega

open TwoAdicValuation in
/- English proof (translation)
Introduce `N a ha ha2`. Use `haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩`. Use `split_ifs with h1`. Rewrite using `[h1, orderOf_one]`. Establish `hv : ∀ j : ℕ, 1 ≤ j → padicValInt 2 (a ^ 2 ^ j - 1) + 1 = padicValInt 2 (a ^ 2 - 1) + j`.

Introduce `j hj`. Use `val_even a ha ha2 (2 ^ j) (by positivity) (Nat.even_pow.mpr ⟨even_two, by omega⟩)` as an intermediate fact. Rewrite `this` using `[padicValNat.prime_pow]`. Then use the resulting hypothesis. Establish `hpow : ∀ j : ℕ, ((a : ZMod (2 ^ N)) ^ 2 ^ j = 1 ↔ N ≤ padicValInt 2 (a ^ 2 ^ j - 1))` using `fun j => powEq N (2 ^ j) a (pow_sub_one_ne a ha2 _ (by positivity))`. Use `set K := max 1 (N + 1 - padicValInt 2 (a ^ 2 - 1)) with hK`.

Establish `hK1 : 1 ≤ K` using `le_max_left _ _`. Establish `hK2 : N + 1 - padicValInt 2 (a ^ 2 - 1) ≤ K` using `le_max_right _ _`. Establish `hK3 : K = 1 ∨ K = N + 1 - padicValInt 2 (a ^ 2 - 1)` using `max_choice _ _`. Use `clear_value K`. Take `⟨n, rfl⟩ : ∃ n, K = n + 1` from `⟨K - 1, by omega⟩`.

Apply `orderOf_eq_prime_pow` to reduce the goal to its premises. Break down `Nat.eq_zero_or_pos n with h0 | h0` into its components or cases. Rewrite using `[h0, pow_zero, pow_one]`. Conclude with `h1`. Rewrite using `[hpow]`.

Use `hv n h0` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hpow]`. Use `hv (n + 1) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem twoAdicOrder : TwoAdicOrder := by
  intro N a ha ha2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  split_ifs with h1
  · rw [h1, orderOf_one]
  · have hv : ∀ j : ℕ, 1 ≤ j →
        padicValInt 2 (a ^ 2 ^ j - 1) + 1 = padicValInt 2 (a ^ 2 - 1) + j := by
      intro j hj
      have := val_even a ha ha2 (2 ^ j) (by positivity) (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      rwa [padicValNat.prime_pow] at this
    have hpow : ∀ j : ℕ,
        ((a : ZMod (2 ^ N)) ^ 2 ^ j = 1 ↔ N ≤ padicValInt 2 (a ^ 2 ^ j - 1)) := fun j =>
      powEq N (2 ^ j) a (pow_sub_one_ne a ha2 _ (by positivity))
    set K := max 1 (N + 1 - padicValInt 2 (a ^ 2 - 1)) with hK
    have hK1 : 1 ≤ K := le_max_left _ _
    have hK2 : N + 1 - padicValInt 2 (a ^ 2 - 1) ≤ K := le_max_right _ _
    have hK3 : K = 1 ∨ K = N + 1 - padicValInt 2 (a ^ 2 - 1) := max_choice _ _
    clear_value K
    obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
    apply orderOf_eq_prime_pow
    · rcases Nat.eq_zero_or_pos n with h0 | h0
      · rw [h0, pow_zero, pow_one]; exact h1
      · rw [hpow]
        have := hv n h0
        omega
    · rw [hpow]
      have := hv (n + 1) (by omega)
      omega

end Formalism.TwoAdicCyclotomicDecomposition
