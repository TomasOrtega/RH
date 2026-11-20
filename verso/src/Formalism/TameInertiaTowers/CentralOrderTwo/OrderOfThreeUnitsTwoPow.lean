import Mathlib
import Formalism.TameInertiaTowers.StatementGroup
import Formalism.TameInertiaTowers.CentralOrderTwo.TwoAdic

namespace Formalism.TwoAdicCyclotomicDecomposition

namespace AdmissibleUnits

def r4 (N : ℕ) (h : 4 ∣ 2 ^ N) : (ZMod (2 ^ N))ˣ →* ZMod 4 :=
  (ZMod.castHom h (ZMod 4)).toMonoidHom.comp (Units.coeHom _)

def r8 (N : ℕ) (h : 8 ∣ 2 ^ N) : (ZMod (2 ^ N))ˣ →* ZMod 8 :=
  (ZMod.castHom h (ZMod 8)).toMonoidHom.comp (Units.coeHom _)

/- English proof (translation)
Unfold `u5`. Use `show (ZMod.castHom h (ZMod 4)) ((5 : ℕ) : ZMod (2 ^ N)) = 1`. Rewrite using `[map_natCast]`. Evaluate the decidable proposition.
-/
lemma mod_four_reduction_five (N : ℕ) (h : 4 ∣ 2 ^ N) : r4 N h (u5 N) = 1 := by
  unfold u5
  show (ZMod.castHom h (ZMod 4)) ((5 : ℕ) : ZMod (2 ^ N)) = 1
  rw [map_natCast]
  decide

/- English proof (translation)
Use `show (ZMod.castHom h (ZMod 4)) (((-1 : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N))) = -1`. Rewrite using `[Units.val_neg, Units.val_one, map_neg, map_one]`.
-/
lemma mod_four_reduction_neg_one (N : ℕ) (h : 4 ∣ 2 ^ N) : r4 N h (-1) = -1 := by
  show (ZMod.castHom h (ZMod 4)) (((-1 : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N))) = -1
  rw [Units.val_neg, Units.val_one, map_neg, map_one]

/- English proof (translation)
Unfold `u3`. Use `show (ZMod.castHom h (ZMod 8)) ((3 : ℕ) : ZMod (2 ^ N)) = 3`. Rewrite using `[map_natCast]`. Evaluate the decidable proposition.
-/
lemma mod_eight_reduction_three (N : ℕ) (h : 8 ∣ 2 ^ N) : r8 N h (u3 N) = 3 := by
  unfold u3
  show (ZMod.castHom h (ZMod 8)) ((3 : ℕ) : ZMod (2 ^ N)) = 3
  rw [map_natCast]
  decide

/- English proof (translation)
Use `show (ZMod.castHom h (ZMod 8)) (((-1 : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N))) = -1`. Rewrite using `[Units.val_neg, Units.val_one, map_neg, map_one]`.
-/
lemma mod_eight_reduction_neg_one (N : ℕ) (h : 8 ∣ 2 ^ N) : r8 N h (-1) = -1 := by
  show (ZMod.castHom h (ZMod 8)) (((-1 : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N))) = -1
  rw [Units.val_neg, Units.val_one, map_neg, map_one]

/- English proof (translation)
Introduce `h`. Establish `h4 : 4 ∣ 2 ^ (n + 2)` using `⟨2 ^ n, by ring⟩`. Use `congrArg (r4 (n + 2) h4) h` as an intermediate fact. Rewrite `this` using `[mod_four_reduction_neg_one, map_one]`. Conclude with `absurd this (by decide)`.
-/
lemma neg_one_ne_one (n : ℕ) : (-1 : (ZMod (2 ^ (n + 2)))ˣ) ≠ 1 := by
  intro h
  have h4 : 4 ∣ 2 ^ (n + 2) := ⟨2 ^ n, by ring⟩
  have := congrArg (r4 (n + 2) h4) h
  rw [mod_four_reduction_neg_one, map_one] at this
  exact absurd this (by decide)

/- English proof (translation)
Conclude with `(Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 h)`.
-/
lemma mem_zpowers_nat {G : Type*} [Group G] [Finite G] {x y : G}
    (h : y ∈ Subgroup.zpowers x) : ∃ k : ℕ, x ^ k = y := by
  exact (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 h)

/- English proof (translation)
Introduce `hm`. Take `⟨k, hk⟩` from `mem_zpowers_nat hm`. Establish `h4 : 4 ∣ 2 ^ (n + 2)` using `⟨2 ^ n, by ring⟩`. Use `congrArg (r4 (n + 2) h4) hk` as an intermediate fact. Rewrite `this` using `[map_pow, mod_four_reduction_five, mod_four_reduction_neg_one, one_pow]`.

Conclude with `absurd this (by decide)`.
-/
lemma neg_not_mem_five (n : ℕ) :
    (-1 : (ZMod (2 ^ (n + 2)))ˣ) ∉ Subgroup.zpowers (u5 (n + 2)) := by
  intro hm
  obtain ⟨k, hk⟩ := mem_zpowers_nat hm
  have h4 : 4 ∣ 2 ^ (n + 2) := ⟨2 ^ n, by ring⟩
  have := congrArg (r4 (n + 2) h4) hk
  rw [map_pow, mod_four_reduction_five, mod_four_reduction_neg_one, one_pow] at this
  exact absurd this (by decide)

/- English proof (translation)
Introduce `hm`. Take `⟨k, hk⟩` from `mem_zpowers_nat hm`. Establish `h8 : 8 ∣ 2 ^ (n + 3)` using `⟨2 ^ n, by ring⟩`. Use `congrArg (r8 (n + 3) h8) hk` as an intermediate fact. Rewrite `this` using `[map_pow, mod_eight_reduction_three, mod_eight_reduction_neg_one]`.

Establish `h9 : (3 : ZMod 8) ^ 2 = 1` using `by decide`. Break down `Nat.even_or_odd' k with ⟨m, rfl | rfl⟩` into its components or cases. Rewrite `this` using `[pow_mul, h9, one_pow]`. Conclude with `absurd this (by decide)`. Rewrite `this` using `[pow_succ, pow_mul, h9, one_pow, one_mul]`.

Conclude with `absurd this (by decide)`.
-/
lemma neg_not_mem_three (n : ℕ) :
    (-1 : (ZMod (2 ^ (n + 3)))ˣ) ∉ Subgroup.zpowers (u3 (n + 3)) := by
  intro hm
  obtain ⟨k, hk⟩ := mem_zpowers_nat hm
  have h8 : 8 ∣ 2 ^ (n + 3) := ⟨2 ^ n, by ring⟩
  have := congrArg (r8 (n + 3) h8) hk
  rw [map_pow, mod_eight_reduction_three, mod_eight_reduction_neg_one] at this
  have h9 : (3 : ZMod 8) ^ 2 = 1 := by decide
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rw [pow_mul, h9, one_pow] at this
    exact absurd this (by decide)
  · rw [pow_succ, pow_mul, h9, one_pow, one_mul] at this
    exact absurd this (by decide)

/- English proof (translation)
Rewrite using `[Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos n)]`. Simplify using the standard rewrite rules.
-/
lemma card_units (n : ℕ) : Nat.card (ZMod (2 ^ (n + 1)))ˣ = 2 ^ n := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos n)]
  simp

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨m0, by simp⟩`. Consider the case `succ k ih`. Take `⟨m, hm⟩` from `ih`.

Use `⟨m + 2 ^ (i + k) * (2 * m + 1) ^ 2, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ 2 k, pow_mul, hm]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma exists_one_add_two_pow_odd_pow_two_pow_eq (i m0 : ℕ) : ∀ k : ℕ, ∃ m : ℕ,
    (1 + 2 ^ (i + 2) * (2 * m0 + 1)) ^ (2 ^ k) = 1 + 2 ^ (k + (i + 2)) * (2 * m + 1) := by
  intro k
  induction k with
  | zero => exact ⟨m0, by simp⟩
  | succ k ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨m + 2 ^ (i + k) * (2 * m + 1) ^ 2, ?_⟩
    rw [pow_succ 2 k, pow_mul, hm]
    ring

/- English proof (translation)
Establish `h : ((2 ^ N : ℕ) : ZMod (2 ^ N)) = 0` using `ZMod.natCast_self _`. Rewrite using `[Nat.cast_add, Nat.cast_mul, h, zero_mul, add_zero, Nat.cast_one]`.
-/
private lemma natCast_one_add_two_pow_mul_eq_one (N q : ℕ) : ((1 + 2 ^ N * q : ℕ) : ZMod (2 ^ N)) = 1 := by
  have h : ((2 ^ N : ℕ) : ZMod (2 ^ N)) = 0 := ZMod.natCast_self _
  rw [Nat.cast_add, Nat.cast_mul, h, zero_mul, add_zero, Nat.cast_one]

/- English proof (translation)
Introduce `h`. Establish `h' : ((1 + 2 ^ N * (2 * m + 1) : ℕ) : ZMod (2 ^ (N + 1))) = ((1 : ℕ) : ZMod (2 ^ (N + 1)))`. Rewrite using `[h, Nat.cast_one]`. Rewrite `h'` using `[ZMod.natCast_eq_natCast_iff]`. Establish `h2` using `(Nat.modEq_iff_dvd' (Nat.le_add_right 1 _)).1 h'.symm`.

Rewrite `h2` using `[Nat.add_sub_cancel_left, pow_succ]`. Establish `h3` using `Nat.dvd_of_mul_dvd_mul_left (pow_pos two_pos N) h2`. Use linear arithmetic over natural numbers and integers.
-/
private lemma natCast_one_add_two_pow_odd_ne_one (N m : ℕ) :
    ((1 + 2 ^ N * (2 * m + 1) : ℕ) : ZMod (2 ^ (N + 1))) ≠ 1 := by
  intro h
  have h' : ((1 + 2 ^ N * (2 * m + 1) : ℕ) : ZMod (2 ^ (N + 1))) = ((1 : ℕ) : ZMod (2 ^ (N + 1))) := by
    rw [h, Nat.cast_one]
  rw [ZMod.natCast_eq_natCast_iff] at h'
  have h2 := (Nat.modEq_iff_dvd' (Nat.le_add_right 1 _)).1 h'.symm
  rw [Nat.add_sub_cancel_left, pow_succ] at h2
  have h3 := Nat.dvd_of_mul_dvd_mul_left (pow_pos two_pos N) h2
  omega

/- English proof (translation)
Rewrite using `[Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, Nat.cast_pow]`.
-/
private lemma unitOfCoprime_pow_eq_one_iff (N a e : ℕ) (h : Nat.Coprime a (2 ^ N)) :
    (ZMod.unitOfCoprime a h) ^ e = 1 ↔ ((a ^ e : ℕ) : ZMod (2 ^ N)) = 1 := by
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, Nat.cast_pow]

/- English proof (translation)
Unfold `u5`. Consider the cases of `n with`. Consider the case `zero`. Rewrite using `[pow_zero, orderOf_eq_one_iff]`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[ZMod.coe_unitOfCoprime, Units.val_one]`. Evaluate the decidable proposition. Consider the case `succ n`. Apply `orderOf_eq_prime_pow` to reduce the goal to its premises. Rewrite using `[unitOfCoprime_pow_eq_one_iff]`.

Take `⟨m, hm⟩` from `exists_one_add_two_pow_odd_pow_two_pow_eq 0 0 n`. Rewrite using `[show (5 : ℕ) = 1 + 2 ^ (0 + 2) * (2 * 0 + 1) by norm_num, hm]`. Conclude with `natCast_one_add_two_pow_odd_ne_one _ _`. Rewrite using `[unitOfCoprime_pow_eq_one_iff]`. Take `⟨m, hm⟩` from `exists_one_add_two_pow_odd_pow_two_pow_eq 0 0 (n + 1)`.

Rewrite using `[show (5 : ℕ) = 1 + 2 ^ (0 + 2) * (2 * 0 + 1) by norm_num, hm]`. Conclude with `natCast_one_add_two_pow_mul_eq_one _ _`.
-/
lemma orderOf_five_units_two_pow (n : ℕ) : orderOf (u5 (n + 2)) = 2 ^ n := by
  unfold u5
  cases n with
  | zero =>
    rw [pow_zero, orderOf_eq_one_iff]
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime, Units.val_one]
    decide
  | succ n =>
    apply orderOf_eq_prime_pow
    · rw [unitOfCoprime_pow_eq_one_iff]
      obtain ⟨m, hm⟩ := exists_one_add_two_pow_odd_pow_two_pow_eq 0 0 n
      rw [show (5 : ℕ) = 1 + 2 ^ (0 + 2) * (2 * 0 + 1) by norm_num, hm]
      exact natCast_one_add_two_pow_odd_ne_one _ _
    · rw [unitOfCoprime_pow_eq_one_iff]
      obtain ⟨m, hm⟩ := exists_one_add_two_pow_odd_pow_two_pow_eq 0 0 (n + 1)
      rw [show (5 : ℕ) = 1 + 2 ^ (0 + 2) * (2 * 0 + 1) by norm_num, hm]
      exact natCast_one_add_two_pow_mul_eq_one _ _

/- English proof (translation)
Unfold `u3`. Apply `orderOf_eq_prime_pow` to reduce the goal to its premises. Rewrite using `[unitOfCoprime_pow_eq_one_iff]`. Consider the cases of `n with`. Consider the case `zero => decide`.

Consider the case `succ n`. Take `⟨m, hm⟩` from `exists_one_add_two_pow_odd_pow_two_pow_eq 1 0 n`. Rewrite using `[pow_succ 2 n, pow_mul' 3 (2 ^ n) 2, show (3 : ℕ) ^ 2 = 1 + 2 ^ (1 + 2) * (2 * 0 + 1) by norm_num, hm]`. Conclude with `natCast_one_add_two_pow_odd_ne_one _ _`. Rewrite using `[unitOfCoprime_pow_eq_one_iff]`.

Take `⟨m, hm⟩` from `exists_one_add_two_pow_odd_pow_two_pow_eq 1 0 n`. Rewrite using `[pow_succ 2 n, pow_mul' 3 (2 ^ n) 2, show (3 : ℕ) ^ 2 = 1 + 2 ^ (1 + 2) * (2 * 0 + 1) by norm_num, hm]`. Conclude with `natCast_one_add_two_pow_mul_eq_one _ _`.
-/
lemma orderOf_three_units_two_pow (n : ℕ) : orderOf (u3 (n + 3)) = 2 ^ (n + 1) := by
  unfold u3
  apply orderOf_eq_prime_pow
  · rw [unitOfCoprime_pow_eq_one_iff]
    cases n with
    | zero => decide
    | succ n =>
      obtain ⟨m, hm⟩ := exists_one_add_two_pow_odd_pow_two_pow_eq 1 0 n
      rw [pow_succ 2 n, pow_mul' 3 (2 ^ n) 2,
        show (3 : ℕ) ^ 2 = 1 + 2 ^ (1 + 2) * (2 * 0 + 1) by norm_num, hm]
      exact natCast_one_add_two_pow_odd_ne_one _ _
  · rw [unitOfCoprime_pow_eq_one_iff]
    obtain ⟨m, hm⟩ := exists_one_add_two_pow_odd_pow_two_pow_eq 1 0 n
    rw [pow_succ 2 n, pow_mul' 3 (2 ^ n) 2,
      show (3 : ℕ) ^ 2 = 1 + 2 ^ (1 + 2) * (2 * 0 + 1) by norm_num, hm]
    exact natCast_one_add_two_pow_mul_eq_one _ _

/- English proof (translation)
Establish `h4 : 4 ∣ 2 ^ (n + 3)` using `⟨2 ^ (n + 1), by ring⟩`. Establish `hr : ∀ c : Bool, r4 (n + 3) h4 (if c then -1 else 1) = if c then -1 else 1`. Introduce `c`. Consider the cases of `c`. Conclude with `map_one _`.

Conclude with `mod_four_reduction_neg_one _ _`. Use `congrArg (r4 (n + 3) h4) h` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, hr, hr, map_pow, map_pow, mod_four_reduction_five, one_pow, one_pow, mul_one, mul_one]`. Apply the tactic sequence `cases b <;> cases b'`. Both sides reduce to the same expression.

Conclude with `absurd this (by decide)`. Conclude with `absurd this (by decide)`. Both sides reduce to the same expression.
-/
lemma sign_eq (n : ℕ) {b b' : Bool} {k k' : ℕ}
    (h : (if b then -1 else 1) * u5 (n + 3) ^ k = (if b' then -1 else 1) * u5 (n + 3) ^ k') :
    b = b' := by
  have h4 : 4 ∣ 2 ^ (n + 3) := ⟨2 ^ (n + 1), by ring⟩
  have hr : ∀ c : Bool, r4 (n + 3) h4 (if c then -1 else 1) = if c then -1 else 1 := by
    intro c
    cases c
    · exact map_one _
    · exact mod_four_reduction_neg_one _ _
  have := congrArg (r4 (n + 3) h4) h
  rw [map_mul, map_mul, hr, hr, map_pow, map_pow, mod_four_reduction_five, one_pow, one_pow, mul_one, mul_one] at this
  cases b <;> cases b'
  · rfl
  · exact absurd this (by decide)
  · exact absurd this (by decide)
  · rfl

/- English proof (translation)
Introduce and unpack `⟨b, k⟩ ⟨b', k'⟩ h`. Establish `h' : (if b then -1 else 1) * u5 (n + 3) ^ (k : ℕ) = (if b' then -1 else 1) * u5 (n + 3) ^ (k' : ℕ)` using `h`. Establish `hb : b = b'` using `sign_eq n h'`. Substitute `hb` using the available equality. Establish `h2 : u5 (n + 3) ^ (k : ℕ) = u5 (n + 3) ^ (k' : ℕ)` using `mul_left_cancel h'`.

Establish `ho : orderOf (u5 (n + 3)) = 2 ^ (n + 1)` using `orderOf_five_units_two_pow (n + 1)`. Rewrite `h2` using `[pow_inj_mod, ho, Nat.mod_eq_of_lt k.2, Nat.mod_eq_of_lt k'.2]`. Conclude with `Prod.ext rfl (Fin.ext h2)`.
-/
lemma inj (n : ℕ) : Function.Injective (fun p : Bool × Fin (2 ^ (n + 1)) =>
    (if p.1 then -1 else 1) * u5 (n + 3) ^ (p.2 : ℕ)) := by
  rintro ⟨b, k⟩ ⟨b', k'⟩ h
  have h' : (if b then -1 else 1) * u5 (n + 3) ^ (k : ℕ) =
      (if b' then -1 else 1) * u5 (n + 3) ^ (k' : ℕ) := h
  have hb : b = b' := sign_eq n h'
  subst hb
  have h2 : u5 (n + 3) ^ (k : ℕ) = u5 (n + 3) ^ (k' : ℕ) := mul_left_cancel h'
  have ho : orderOf (u5 (n + 3)) = 2 ^ (n + 1) := orderOf_five_units_two_pow (n + 1)
  rw [pow_inj_mod, ho, Nat.mod_eq_of_lt k.2, Nat.mod_eq_of_lt k'.2] at h2
  exact Prod.ext rfl (Fin.ext h2)

/- English proof (translation)
Take `⟨k, rfl⟩` from `mem_zpowers_nat hy`. Break down `Nat.even_or_odd' k with ⟨m, rfl | rfl⟩` into its components or cases. Use `left`. Rewrite using `[pow_mul, hg, one_pow]`. Use `right`.

Rewrite using `[pow_succ, pow_mul, hg, one_pow, one_mul]`.
-/
lemma zpowers_sq {G : Type*} [Group G] [Finite G] {g y : G} (hg : g ^ 2 = 1)
    (hy : y ∈ Subgroup.zpowers g) : y = 1 ∨ y = g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_nat hy
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [pow_mul, hg, one_pow]
  · right
    rw [pow_succ, pow_mul, hg, one_pow, one_mul]

/- English proof (translation)
Apply `Nat.dvd_antisymm` to reduce the goal to its premises. Conclude with `orderOf_map_dvd (QuotientGroup.mk' _) x`. Apply `orderOf_dvd_of_pow_eq_one` to reduce the goal to its premises. Establish `h1 : (QuotientGroup.mk (s` using `Subgroup.zpowers g) x) ^ orderOf (QuotientGroup.mk (s := Subgroup.zpowers g) x) = 1 := pow_orderOf_eq_one _`. Rewrite `h1` using `[← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]`.

Break down `zpowers_sq hg h1 with h2 | h2` into its components or cases. Conclude with `h2`. Conclude with `absurd (by rw [← h2]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _) hx`.
-/
lemma orderOf_mk_eq {G : Type*} [CommGroup G] [Finite G] {x g : G} (hg : g ^ 2 = 1)
    (hx : g ∉ Subgroup.zpowers x) :
    orderOf (QuotientGroup.mk (s := Subgroup.zpowers g) x) = orderOf x := by
  apply Nat.dvd_antisymm
  · exact orderOf_map_dvd (QuotientGroup.mk' _) x
  · apply orderOf_dvd_of_pow_eq_one
    have h1 : (QuotientGroup.mk (s := Subgroup.zpowers g) x) ^
        orderOf (QuotientGroup.mk (s := Subgroup.zpowers g) x) = 1 := pow_orderOf_eq_one _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    rcases zpowers_sq hg h1 with h2 | h2
    · exact h2
    · exact absurd (by rw [← h2]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _) hx

/- English proof (translation)
Establish `h1` using `Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ))`. Rewrite `h1` using `[Nat.card_zpowers, orderOf_eq_prime (neg_one_sq) (neg_one_ne_one n)]`. Establish `h2 : Nat.card (ZMod (2 ^ (n + 2)))ˣ = 2 ^ n * 2`. Use `card_units (n + 1)` as an intermediate fact. Rewrite `this` using `[pow_succ]`.

Conclude with `this`. Rewrite `h1` using `[h2]`. Conclude with `(Nat.eq_of_mul_eq_mul_right two_pos h1).symm`.
-/
lemma card_quot (n : ℕ) : Nat.card ((ZMod (2 ^ (n + 2)))ˣ ⧸
    Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ)) = 2 ^ n := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ))
  rw [Nat.card_zpowers, orderOf_eq_prime (neg_one_sq) (neg_one_ne_one n)] at h1
  have h2 : Nat.card (ZMod (2 ^ (n + 2)))ˣ = 2 ^ n * 2 := by
    have := card_units (n + 1)
    rw [pow_succ] at this
    exact this
  rw [h2] at h1
  exact (Nat.eq_of_mul_eq_mul_right two_pos h1).symm

end AdmissibleUnits

open AdmissibleUnits in
/- English proof (translation)
Unfold `UnitsTwoPow`. Introduce `n`. Use `⟨card_units (n + 2), orderOf_five_units_two_pow (n + 1), orderOf_three_units_two_pow n, neg_not_mem_five (n + 1), neg_not_mem_three n, ?_⟩` and prove the remaining obligations. Introduce `u`. Establish `hc : Nat.card (ZMod (2 ^ (n + 3)))ˣ = 2 ^ (n + 2)` using `card_units (n + 2)`.

Establish `hcard : Fintype.card (Bool × Fin (2 ^ (n + 1))) = Fintype.card (ZMod (2 ^ (n + 3)))ˣ`. Rewrite using `[Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, ← Nat.card_eq_fintype_card, hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hbij` using `(Fintype.bijective_iff_injective_and_card _).mpr ⟨inj n, hcard⟩`. Take `⟨p, hp⟩` from `hbij.2 u`.

Conclude with `⟨p, hp.symm, fun q hq => hbij.1 (hq.symm.trans hp.symm)⟩`.
-/
theorem unitsTwoPow : UnitsTwoPow := by
  unfold UnitsTwoPow
  intro n
  refine ⟨card_units (n + 2), orderOf_five_units_two_pow (n + 1), orderOf_three_units_two_pow n, neg_not_mem_five (n + 1),
    neg_not_mem_three n, ?_⟩
  intro u
  have hc : Nat.card (ZMod (2 ^ (n + 3)))ˣ = 2 ^ (n + 2) := card_units (n + 2)
  have hcard : Fintype.card (Bool × Fin (2 ^ (n + 1))) = Fintype.card (ZMod (2 ^ (n + 3)))ˣ := by
    rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, ← Nat.card_eq_fintype_card, hc]
    ring
  have hbij := (Fintype.bijective_iff_injective_and_card _).mpr ⟨inj n, hcard⟩
  obtain ⟨p, hp⟩ := hbij.2 u
  exact ⟨p, hp.symm, fun q hq => hbij.1 (hq.symm.trans hp.symm)⟩

open AdmissibleUnits in
/- English proof (translation)
Unfold `QuotCyclic`. Introduce `n`. Establish `hsq : (-1 : (ZMod (2 ^ (n + 2)))ˣ) ^ 2 = 1` using `neg_one_sq`. Establish `h5 : orderOf (QuotientGroup.mk (s` using `Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ)) (u5 (n + 2))) = 2 ^ n := by`. Rewrite using `[orderOf_mk_eq hsq (neg_not_mem_five n), orderOf_five_units_two_pow n]`.

Use `⟨isCyclic_of_orderOf_eq_card _ (h5.trans (card_quot n).symm), card_quot n, h5, ?_⟩` and prove the remaining obligations. Consider the cases of `n with`. Consider the case `zero`. Rewrite using `[pow_zero, orderOf_eq_one_iff, QuotientGroup.eq_one_iff]`. Establish `h3 : u3 (0 + 2) = -1`.

Unfold `u3`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[ZMod.coe_unitOfCoprime, Units.val_neg, Units.val_one]`. Evaluate the decidable proposition. Rewrite using `[h3]`.

Conclude with `Subgroup.mem_zpowers _`. Consider the case `succ n => show orderOf (QuotientGroup.mk (s := Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 3)))ˣ)) (u3 (n + 3))) = 2 ^ (n + 1)`. Rewrite using `[orderOf_mk_eq neg_one_sq (neg_not_mem_three n)]`. Conclude with `orderOf_three_units_two_pow n`.
-/
theorem quotCyclic : QuotCyclic := by
  unfold QuotCyclic
  intro n
  have hsq : (-1 : (ZMod (2 ^ (n + 2)))ˣ) ^ 2 = 1 := neg_one_sq
  have h5 : orderOf (QuotientGroup.mk (s := Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 2)))ˣ))
      (u5 (n + 2))) = 2 ^ n := by
    rw [orderOf_mk_eq hsq (neg_not_mem_five n), orderOf_five_units_two_pow n]
  refine ⟨isCyclic_of_orderOf_eq_card _ (h5.trans (card_quot n).symm), card_quot n, h5, ?_⟩
  cases n with
  | zero =>
    rw [pow_zero, orderOf_eq_one_iff, QuotientGroup.eq_one_iff]
    have h3 : u3 (0 + 2) = -1 := by
      unfold u3
      apply Units.ext
      rw [ZMod.coe_unitOfCoprime, Units.val_neg, Units.val_one]
      decide
    rw [h3]
    exact Subgroup.mem_zpowers _
  | succ n =>
    show orderOf (QuotientGroup.mk (s := Subgroup.zpowers (-1 : (ZMod (2 ^ (n + 3)))ˣ))
      (u3 (n + 3))) = 2 ^ (n + 1)
    rw [orderOf_mk_eq neg_one_sq (neg_not_mem_three n)]
    exact orderOf_three_units_two_pow n

end Formalism.TwoAdicCyclotomicDecomposition
