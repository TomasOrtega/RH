import Formalism.PairingDivisors.StatementN

namespace GlobalTheory

open Formalism.PairingDivisionLocalBalance

/- English proof (translation)
Use `haveI := Fact.mk hl`. Take `⟨g, hg⟩` from `IsCyclic.exists_generator (α := (ZMod l)ˣ)`. Establish `hord : orderOf g = l - 1`. Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hl]`. Use `⟨(g : ZMod l).val, ?_, ZMod.val_coe_unit_coprime g, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `h push_neg at h interval_cases hv : (g : ZMod l).val`. Establish `: (g : ZMod l) = 0` using `(ZMod.val_eq_zero _).mp hv`. Conclude with `(Units.ne_zero g) this`. Establish `h1 : (g : ZMod l) = 1`. Rewrite using `[← ZMod.natCast_zmod_val (g : ZMod l), hv, Nat.cast_one]`.

Establish `: g = 1` using `Units.ext h1`. Rewrite `hord` using `[this, orderOf_one]`. Conclude with `hn (by rw [← hord]; exact one_dvd n)`. Introduce `hdvd`. Establish `hpos : 1 ≤ (g : ZMod l).val ^ n`.

Apply `Nat.one_le_pow` to reduce the goal to its premises. Rewrite using `[Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]`. Conclude with `Units.ne_zero g`. Establish `h0 : (((g : ZMod l).val ^ n - 1 : ℕ) : ZMod l) = 0` using `(ZMod.natCast_eq_zero_iff _ _).mpr hdvd`. Rewrite `h0` using `[Nat.cast_sub hpos, Nat.cast_pow, ZMod.natCast_zmod_val, Nat.cast_one, sub_eq_zero]`.

Establish `hgn : g ^ n = 1` using `Units.ext (by simpa using h0)`. Conclude with `hn (hord ▸ orderOf_dvd_of_pow_eq_one hgn)`.
-/
theorem exists_pow_ne_one_mod (l n : ℕ) (hl : l.Prime) (hn : ¬ (l - 1) ∣ n) :
    ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ ¬ l ∣ a ^ n - 1 := by
  haveI := Fact.mk hl
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have hord : orderOf g = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hl]
  refine ⟨(g : ZMod l).val, ?_, ZMod.val_coe_unit_coprime g, ?_⟩
  · by_contra h
    push_neg at h
    interval_cases hv : (g : ZMod l).val
    · have : (g : ZMod l) = 0 := (ZMod.val_eq_zero _).mp hv
      exact (Units.ne_zero g) this
    · have h1 : (g : ZMod l) = 1 := by
        rw [← ZMod.natCast_zmod_val (g : ZMod l), hv, Nat.cast_one]
      have : g = 1 := Units.ext h1
      rw [this, orderOf_one] at hord
      exact hn (by rw [← hord]; exact one_dvd n)
  · intro hdvd
    have hpos : 1 ≤ (g : ZMod l).val ^ n := by
      apply Nat.one_le_pow
      rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]
      exact Units.ne_zero g
    have h0 : (((g : ZMod l).val ^ n - 1 : ℕ) : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_sub hpos, Nat.cast_pow, ZMod.natCast_zmod_val, Nat.cast_one, sub_eq_zero] at h0
    have hgn : g ^ n = 1 := Units.ext (by simpa using h0)
    exact hn (hord ▸ orderOf_dvd_of_pow_eq_one hgn)

/- English proof (translation)
Introduce `l n hl hn2 hne`. Use `haveI := Fact.mk hl`. Establish `hn0 : n ≠ 0` using `by omega`. Unfold `mE`. Distinguish the cases in `h2 : l = 2`.

Substitute `h2` using the available equality. Use `⟨3, by norm_num, by norm_num, ?_⟩` and prove the remaining obligations. Establish `h` using `padicValNat.pow_two_sub_one (x := 3) (n := n) (by norm_num) (by norm_num) hn0 hne`. Establish `h4 : padicValNat 2 (3 + 1) = 2`. Evaluate the numerical expressions.

Rewrite using `[show (4:ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]`. Establish `h2' : padicValNat 2 (3 - 1) = 1` using `by norm_num`. Rewrite `h` using `[h4, h2']`. Simplify using `only [if_true]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [h2, if_false]`. Establish `hodd : Odd l` using `hl.odd_of_ne_two h2`. Distinguish the cases in `hd : (l - 1) ∣ n`. Simplify using `only [hd, if_true]`. Use `⟨l + 1, by have := hl.two_le; omega, ?_, ?_⟩` and prove the remaining obligations.

Use `first`. Consider the case `exact (Nat.coprime_succ_self l)`. Consider the case `exact (Nat.coprime_self_succ l)`. Consider the case `simp`. Establish `h` using `padicValNat.pow_sub_pow (p := l) (x := l + 1) (y := 1) hodd (by have := hl.one_lt; omega) (by simp) (by`.

Introduce `hdv`. Establish `: l ∣ 1` using `(Nat.dvd_add_right (dvd_refl l)).mp hdv`. Conclude with `hl.one_lt.ne' (Nat.dvd_one.mp this)) hn0`. Rewrite `h` using `[one_pow]`. Rewrite using `[h, show l + 1 - 1 = l by omega, padicValNat_self]`.

Simplify using `only [hd, if_false]`. Take `⟨a, ha2, hac, hnd⟩` from `exists_pow_ne_one_mod l n hl hd`. Conclude with `⟨a, ha2, hac, padicValNat.eq_zero_of_not_dvd hnd⟩`.
-/
theorem cmValues_minPadicVal_bound : MinVal := by
  intro l n hl hn2 hne
  haveI := Fact.mk hl
  have hn0 : n ≠ 0 := by omega
  unfold mE
  by_cases h2 : l = 2
  · subst h2
    refine ⟨3, by norm_num, by norm_num, ?_⟩
    have h := padicValNat.pow_two_sub_one (x := 3) (n := n) (by norm_num) (by norm_num) hn0 hne
    have h4 : padicValNat 2 (3 + 1) = 2 := by
      norm_num
      rw [show (4:ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    have h2' : padicValNat 2 (3 - 1) = 1 := by norm_num
    rw [h4, h2'] at h
    simp only [if_true]
    omega
  · simp only [h2, if_false]
    have hodd : Odd l := hl.odd_of_ne_two h2
    by_cases hd : (l - 1) ∣ n
    · simp only [hd, if_true]
      refine ⟨l + 1, by have := hl.two_le; omega, ?_, ?_⟩
      · first
          | exact (Nat.coprime_succ_self l)
          | exact (Nat.coprime_self_succ l)
          | simp
      · have h := padicValNat.pow_sub_pow (p := l) (x := l + 1) (y := 1) hodd (by have := hl.one_lt; omega)
          (by simp) (by
            intro hdv
            have : l ∣ 1 := (Nat.dvd_add_right (dvd_refl l)).mp hdv
            exact hl.one_lt.ne' (Nat.dvd_one.mp this)) hn0
        rw [one_pow] at h
        rw [h, show l + 1 - 1 = l by omega, padicValNat_self]
    · simp only [hd, if_false]
      obtain ⟨a, ha2, hac, hnd⟩ := exists_pow_ne_one_mod l n hl hd
      exact ⟨a, ha2, hac, padicValNat.eq_zero_of_not_dvd hnd⟩

end GlobalTheory
