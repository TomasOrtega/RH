import Development.AutomorphicArithmetic.FrobeniusLocalisation.SizeDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.FrobGSpec

open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.FrobeniusOrbits Formalism.HC
open scoped Pointwise

/- English proof (translation)
Take `⟨t, rfl⟩` from `ha`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(h | h)`. Establish `e1 : (2 * t + 1) ^ 2 - 1 = 2 ^ 2 * (t * (t + 1))` using `by ring`. Establish `e2 : (2:ℤ) ^ (k + 1 + 1) = 2 ^ 2 * 2 ^ k` using `by ring`.

Rewrite `h` using `[e1, e2]`. Establish `h' : (2:ℤ) ^ k ∣ t * (t + 1)` using `(mul_dvd_mul_iff_left (by norm_num)).1 h`. Break down `Int.even_or_odd t with ⟨r, hr⟩ | ⟨r, hr⟩` into its components or cases. Establish `hc : IsCoprime ((2:ℤ) ^ k) (t + 1)`. Apply `IsCoprime.pow_left` to reduce the goal to its premises.

Conclude with `⟨-r, 1, by rw [hr]; ring⟩`. Take `⟨c, hc'⟩` from `hc.dvd_of_dvd_mul_right h'`. Conclude with `Or.inl ⟨c, by rw [hc']; ring⟩`. Establish `hc : IsCoprime ((2:ℤ) ^ k) t`. Apply `IsCoprime.pow_left` to reduce the goal to its premises.

Conclude with `⟨-r, 1, by rw [hr]; ring⟩`. Rewrite `h'` using `[mul_comm]`. Take `⟨c, hc'⟩` from `hc.dvd_of_dvd_mul_right h'`. Conclude with `Or.inr ⟨c, by linear_combination 2 * hc'⟩`. It suffices to derive a contradiction.

Establish `h4 : (4:ℤ) ∣ (2:ℤ) ^ (k + 1 + 1)` using `⟨2 ^ k, by ring⟩`. Establish `h5` using `dvd_trans h4 h`. Establish `e1 : (2 * t + 1) ^ 2 + 1 = 4 * (t ^ 2 + t) + 2` using `by ring`. Rewrite `h5` using `[e1]`. Generalize the expression as in `t ^ 2 + t = s at h5`.

Use linear arithmetic over natural numbers and integers. Introduce and unpack `(⟨c, hc⟩ | ⟨c, hc⟩)`. Conclude with `Or.inl ⟨c * (2 ^ k * c + 1), by linear_combination (2 * t + 2 ^ (k + 1) * c + 2) * hc⟩`. Conclude with `Or.inl ⟨c * (2 ^ k * c - 1), by linear_combination (2 * t + 2 ^ (k + 1) * c) * hc⟩`.
-/
private theorem two_pow_dvd_sq_pm_one_iff_of_odd (a : ℤ) (ha : Odd a) (k : ℕ) :
    ((2:ℤ) ^ (k + 1 + 1) ∣ a ^ 2 - 1 ∨ (2:ℤ) ^ (k + 1 + 1) ∣ a ^ 2 + 1) ↔
      ((2:ℤ) ^ (k + 1) ∣ a - 1 ∨ (2:ℤ) ^ (k + 1) ∣ a + 1) := by
  obtain ⟨t, rfl⟩ := ha
  constructor
  · rintro (h | h)
    · have e1 : (2 * t + 1) ^ 2 - 1 = 2 ^ 2 * (t * (t + 1)) := by ring
      have e2 : (2:ℤ) ^ (k + 1 + 1) = 2 ^ 2 * 2 ^ k := by ring
      rw [e1, e2] at h
      have h' : (2:ℤ) ^ k ∣ t * (t + 1) := (mul_dvd_mul_iff_left (by norm_num)).1 h
      rcases Int.even_or_odd t with ⟨r, hr⟩ | ⟨r, hr⟩
      · have hc : IsCoprime ((2:ℤ) ^ k) (t + 1) := by
          apply IsCoprime.pow_left
          exact ⟨-r, 1, by rw [hr]; ring⟩
        obtain ⟨c, hc'⟩ := hc.dvd_of_dvd_mul_right h'
        exact Or.inl ⟨c, by rw [hc']; ring⟩
      · have hc : IsCoprime ((2:ℤ) ^ k) t := by
          apply IsCoprime.pow_left
          exact ⟨-r, 1, by rw [hr]; ring⟩
        rw [mul_comm] at h'
        obtain ⟨c, hc'⟩ := hc.dvd_of_dvd_mul_right h'
        exact Or.inr ⟨c, by linear_combination 2 * hc'⟩
    · exfalso
      have h4 : (4:ℤ) ∣ (2:ℤ) ^ (k + 1 + 1) := ⟨2 ^ k, by ring⟩
      have h5 := dvd_trans h4 h
      have e1 : (2 * t + 1) ^ 2 + 1 = 4 * (t ^ 2 + t) + 2 := by ring
      rw [e1] at h5
      generalize t ^ 2 + t = s at h5
      omega
  · rintro (⟨c, hc⟩ | ⟨c, hc⟩)
    · exact Or.inl ⟨c * (2 ^ k * c + 1), by linear_combination (2 * t + 2 ^ (k + 1) * c + 2) * hc⟩
    · exact Or.inl ⟨c * (2 ^ k * c - 1), by linear_combination (2 * t + 2 ^ (k + 1) * c) * hc⟩

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => intro a _ k`. Simplify using the standard rewrite rules. Consider the case `succ j ih`. Introduce `a ha k`.

Establish `h1 : (a ^ 2) ^ (2 ^ j) = a ^ (2 ^ (j + 1))` using `by rw [← pow_mul, ← pow_succ']`. Establish `h2 : k + 1 + (j + 1) = (k + 1) + 1 + j` using `by omega`. Rewrite using `[← h1, h2, ih (a ^ 2) ha.pow (k + 1)]`. Conclude with `two_pow_dvd_sq_pm_one_iff_of_odd a ha k`.
-/
private theorem two_pow_dvd_pow_two_pow_sub_or_add_iff (j : ℕ) : ∀ (a : ℤ), Odd a → ∀ k : ℕ,
    ((2:ℤ) ^ (k + 1 + j) ∣ a ^ (2 ^ j) - 1 ∨ (2:ℤ) ^ (k + 1 + j) ∣ a ^ (2 ^ j) + 1) ↔
      ((2:ℤ) ^ (k + 1) ∣ a - 1 ∨ (2:ℤ) ^ (k + 1) ∣ a + 1) := by
  induction j with
  | zero => intro a _ k; simp
  | succ j ih =>
    intro a ha k
    have h1 : (a ^ 2) ^ (2 ^ j) = a ^ (2 ^ (j + 1)) := by rw [← pow_mul, ← pow_succ']
    have h2 : k + 1 + (j + 1) = (k + 1) + 1 + j := by omega
    rw [← h1, h2, ih (a ^ 2) ha.pow (k + 1)]
    exact two_pow_dvd_sq_pm_one_iff_of_odd a ha k

/- English proof (translation)
Establish `e1 : ((a : ZMod n) = 1) ↔ (((a - 1 : ℤ) : ZMod n) = 0)` using `by push_cast; exact sub_eq_zero.symm`. Establish `e2 : ((a : ZMod n) = -1) ↔ (((a + 1 : ℤ) : ZMod n) = 0)` using `by push_cast; exact eq_neg_iff_add_eq_zero`. Rewrite using `[e1, e2, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]`.
-/
private theorem cast_eq_one_or_neg_one_iff_dvd (n : ℕ) (a : ℤ) :
    ((a : ZMod n) = 1 ∨ (a : ZMod n) = -1) ↔ ((n : ℤ) ∣ a - 1 ∨ (n : ℤ) ∣ a + 1) := by
  have e1 : ((a : ZMod n) = 1) ↔ (((a - 1 : ℤ) : ZMod n) = 0) := by
    push_cast; exact sub_eq_zero.symm
  have e2 : ((a : ZMod n) = -1) ↔ (((a + 1 : ℤ) : ZMod n) = 0) := by
    push_cast; exact eq_neg_iff_add_eq_zero
  rw [e1, e2, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]

/- English proof (translation)
Introduce `φ H p hp hpN`. Use `haveI := Fact.mk hp`. Take `⟨-, -, -, -, -, v, hv, hx⟩` from `frobG_spec φ H p hpN`. Rewrite using `[hx]`. Use `set x := hcl φ.e v with hxdef`.

Establish `hp2 : p ≠ 2`. Introduce and unpack `rfl`. Conclude with `hpN (HostRaw.two_dvd_condN _)`. Establish `hodd : Odd (p : ℤ)` using `(Int.odd_coe_nat p).2 (hp.odd_of_ne_two hp2)`. Establish `key : ∀ k : ℕ, x ^ k = 1 ↔ ((2:ℤ) ^ (φ.e + 2) ∣ (p : ℤ) ^ k - 1 ∨ (2:ℤ) ^ (φ.e + 2) ∣ (p : ℤ) ^ k + 1)`.

Introduce `k`. Rewrite using `[hxdef, Group.hcl_pow_eq_one]`. Simplify using `only [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, hv]`. Establish `hc` using `cast_eq_one_or_neg_one_iff_dvd (2 ^ (φ.e + 2)) ((p : ℤ) ^ k)`. Move the coercions through the operations in `at hc`.

Conclude with `hc`. Establish `hx4 : x ^ (2 ^ φ.e) = 1`. Rewrite using `[key]`. Establish `h` using `(two_pow_dvd_pow_two_pow_sub_or_add_iff φ.e (p : ℤ) hodd 1).2 (by`. Take `⟨t, ht⟩` from `hodd`.

Rewrite using `[ht]`. Establish `: (2:ℤ) ^ (1 + 1) = 4` using `by norm_num`. Rewrite using `[this]`. Use the proof step `omega)`. Rewrite `h` using `[show 1 + 1 + φ.e = φ.e + 2 by omega]`. Then use the resulting hypothesis.

Take `⟨i, hi, hord⟩` from `(Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx4)`. Establish `cl1 : ∀ j : ℕ, orderOf x ≤ 2 ^ j ↔ ((p : ZMod (2 ^ (φ.e + 2 - j))) = 1 ∨ (p : ZMod (2 ^ (φ.e + 2 - j))) = -1)`. Introduce `j`. Distinguish the cases in `hj : j ≤ φ.e + 1`. Take `⟨m, hm⟩ : ∃ m, φ.e + 2 - j = m + 1` from `⟨φ.e + 1 - j, by omega⟩`.

Rewrite using `[hm]`. Establish `hc` using `cast_eq_one_or_neg_one_iff_dvd (2 ^ (m + 1)) (p : ℤ)`. Move the coercions through the operations in `at hc`. Rewrite using `[hc, ← two_pow_dvd_pow_two_pow_sub_or_add_iff j (p : ℤ) hodd m, show m + 1 + j = φ.e + 2 by omega, ← key, ← orderOf_dvd_iff_pow_eq_one, hord, Nat.pow_dvd_pow_iff_le_right (by norm_num), Nat.pow_le_pow_iff_right (by norm_num)]`. Establish `h0 : φ.e + 2 - j = 0` using `by omega`.

Rewrite using `[h0, hord]`. Use `haveI : Subsingleton (ZMod (2 ^ 0)) := ZMod.subsingleton_iff.2 (by norm_num)`. Prove the components needed by the constructor for the conclusion. Introduce `_`. Conclude with `Or.inl (Subsingleton.elim _ _)`.

Introduce `_`. Conclude with `Nat.pow_le_pow_right (by norm_num) (by omega)`. Use `⟨cl1, ⟨i, hi, hord⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `(cl1 i).1 (le_of_eq hord)`. Establish `hc` using `cast_eq_one_or_neg_one_iff_dvd (2 ^ (φ.e + 2 - i)) (p : ℤ)`.

Move the coercions through the operations in `at hc`. Establish `h2p` using `hp.two_le`. Establish `hb : ((2 ^ (φ.e + 2 - i) : ℕ) : ℤ) ≤ (p : ℤ) + 1`. Use `push_cast`. Break down `hc.1 h with hd | hd` into its components or cases.

Use `Int.le_of_dvd (by omega) hd` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `Int.le_of_dvd (by omega) hd`. Establish `hb' : 2 ^ (φ.e + 2 - i) ≤ p + 1` using `by exact_mod_cast hb`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Use `_ ≤ (p + 1) * 2 ^ i := Nat.mul_le_mul_right _ hb'`. Use `_ = (p + 1) * orderOf x := by rw [hord]`.

Establish `h` using `key 1`. Simplify using `only [pow_one] at h`. Rewrite using `[h]`. Establish `hc` using `cast_eq_one_or_neg_one_iff_dvd (2 ^ (φ.e + 2)) (p : ℤ)`. Move the coercions through the operations in `at hc`.

Rewrite using `[hc]`.
-/
theorem UpperTheory.HF.frob_h_order :
    ∀ (φ : Frame) (H : HostAx φ) (p : ℕ), p.Prime → ¬ p ∣ H.condN →
      (∀ j : ℕ, orderOf (φ.hH (H.frobG p).2) ≤ 2 ^ j ↔
        ((p : ZMod (2 ^ (φ.e + 2 - j))) = 1 ∨ (p : ZMod (2 ^ (φ.e + 2 - j))) = -1)) ∧
      (∃ j ≤ φ.e, orderOf (φ.hH (H.frobG p).2) = 2 ^ j) ∧
      2 ^ (φ.e + 2) ≤ (p + 1) * orderOf (φ.hH (H.frobG p).2) ∧
      (φ.hH (H.frobG p).2 = 1 ↔ ((p : ZMod (2 ^ (φ.e + 2))) = 1 ∨ (p : ZMod (2 ^ (φ.e + 2))) = -1)) := by
  intro φ H p hp hpN
  haveI := Fact.mk hp
  obtain ⟨-, -, -, -, -, v, hv, hx⟩ := frobG_spec φ H p hpN
  rw [hx]
  set x := hcl φ.e v with hxdef
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpN (HostRaw.two_dvd_condN _)
  have hodd : Odd (p : ℤ) := (Int.odd_coe_nat p).2 (hp.odd_of_ne_two hp2)
  have key : ∀ k : ℕ, x ^ k = 1 ↔
      ((2:ℤ) ^ (φ.e + 2) ∣ (p : ℤ) ^ k - 1 ∨ (2:ℤ) ^ (φ.e + 2) ∣ (p : ℤ) ^ k + 1) := by
    intro k
    rw [hxdef, Group.hcl_pow_eq_one]
    simp only [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, hv]
    have hc := cast_eq_one_or_neg_one_iff_dvd (2 ^ (φ.e + 2)) ((p : ℤ) ^ k)
    push_cast at hc
    exact hc
  have hx4 : x ^ (2 ^ φ.e) = 1 := by
    rw [key]
    have h := (two_pow_dvd_pow_two_pow_sub_or_add_iff φ.e (p : ℤ) hodd 1).2 (by
      obtain ⟨t, ht⟩ := hodd
      rw [ht]
      have : (2:ℤ) ^ (1 + 1) = 4 := by norm_num
      rw [this]
      omega)
    rwa [show 1 + 1 + φ.e = φ.e + 2 by omega] at h
  obtain ⟨i, hi, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx4)
  have cl1 : ∀ j : ℕ, orderOf x ≤ 2 ^ j ↔
      ((p : ZMod (2 ^ (φ.e + 2 - j))) = 1 ∨ (p : ZMod (2 ^ (φ.e + 2 - j))) = -1) := by
    intro j
    by_cases hj : j ≤ φ.e + 1
    · obtain ⟨m, hm⟩ : ∃ m, φ.e + 2 - j = m + 1 := ⟨φ.e + 1 - j, by omega⟩
      rw [hm]
      have hc := cast_eq_one_or_neg_one_iff_dvd (2 ^ (m + 1)) (p : ℤ)
      push_cast at hc
      rw [hc, ← two_pow_dvd_pow_two_pow_sub_or_add_iff j (p : ℤ) hodd m, show m + 1 + j = φ.e + 2 by omega, ← key,
        ← orderOf_dvd_iff_pow_eq_one, hord, Nat.pow_dvd_pow_iff_le_right (by norm_num),
        Nat.pow_le_pow_iff_right (by norm_num)]
    · have h0 : φ.e + 2 - j = 0 := by omega
      rw [h0, hord]
      haveI : Subsingleton (ZMod (2 ^ 0)) := ZMod.subsingleton_iff.2 (by norm_num)
      constructor
      · intro _
        exact Or.inl (Subsingleton.elim _ _)
      · intro _
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨cl1, ⟨i, hi, hord⟩, ?_, ?_⟩
  · have h := (cl1 i).1 (le_of_eq hord)
    have hc := cast_eq_one_or_neg_one_iff_dvd (2 ^ (φ.e + 2 - i)) (p : ℤ)
    push_cast at hc
    have h2p := hp.two_le
    have hb : ((2 ^ (φ.e + 2 - i) : ℕ) : ℤ) ≤ (p : ℤ) + 1 := by
      push_cast
      rcases hc.1 h with hd | hd
      · have := Int.le_of_dvd (by omega) hd
        linarith
      · exact Int.le_of_dvd (by omega) hd
    have hb' : 2 ^ (φ.e + 2 - i) ≤ p + 1 := by exact_mod_cast hb
    calc 2 ^ (φ.e + 2) = 2 ^ (φ.e + 2 - i) * 2 ^ i := by
          rw [← pow_add]
          congr 1
          omega
      _ ≤ (p + 1) * 2 ^ i := Nat.mul_le_mul_right _ hb'
      _ = (p + 1) * orderOf x := by rw [hord]
  · have h := key 1
    simp only [pow_one] at h
    rw [h]
    have hc := cast_eq_one_or_neg_one_iff_dvd (2 ^ (φ.e + 2)) (p : ℤ)
    push_cast at hc
    rw [hc]
