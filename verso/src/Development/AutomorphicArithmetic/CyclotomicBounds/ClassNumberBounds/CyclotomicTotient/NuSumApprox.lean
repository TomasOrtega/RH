import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuInf

namespace KStar.Tree

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Assume the negation of the conclusion as `hu`. Establish `: c ∈ IsLocalRing.maximalIdeal ℤ_[l]` using `hu`. Rewrite `this` using `[PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]`. Conclude with `hc this`.
-/
private theorem nsa_isUnit {c : ℤ_[l]} (hc : ¬ (l : ℤ_[l]) ∣ c) : IsUnit c := by
  by_contra hu
  have : c ∈ IsLocalRing.maximalIdeal ℤ_[l] := hu
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
  exact hc this

/- English proof (translation)
Rewrite using `[← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]`.
-/
private theorem nsa_dvd_iff (x : ℤ_[l]) : (l : ℤ_[l]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

/- English proof (translation)
Use `(PadicInt.pow_p_dvd_int_iff (p := l) k (m : ℤ)).1 (by simpa using h)` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
private theorem nsa_nat (k : ℕ) (m : ℕ) (h : (l : ℤ_[l]) ^ k ∣ (m : ℤ_[l])) : l ^ k ∣ m := by
  have := (PadicInt.pow_p_dvd_int_iff (p := l) k (m : ℤ)).1 (by simpa using h)
  exact_mod_cast this

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hpz : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.1 hp`. Establish `hn0 : n ≠ 0` using `by rintro rfl; simp at hn`. Establish `hxy : (l : ℤ) ∣ (1 + (l : ℤ) ^ s) - 1`. Simplify using `using dvd_pow_self (l : ℤ) hs`.

Establish `hx : ¬ (l : ℤ) ∣ 1 + (l : ℤ) ^ s`. Introduce `h`. Conclude with `hpz.not_dvd_one ((dvd_add_left (dvd_pow_self (l : ℤ) hs)).1 h)`. Establish `hs' : emultiplicity (l : ℤ) ((1 + (l : ℤ) ^ s) - 1) = s`. Rewrite using `[add_sub_cancel_left]`.

Conclude with `emultiplicity_pow_self_of_prime hpz s`. Establish `key : emultiplicity (l : ℤ) ((1 + (l : ℤ) ^ s) ^ n - 1 ^ n) = ((s + n.factorization l : ℕ) : ℕ∞)`. Distinguish the cases in `hl : l = 2`. Establish `hnd : ¬ l ∣ n`. Substitute `hl` using the available equality.

Conclude with `hn.not_two_dvd_nat`. Rewrite using `[emultiplicity_pow_sub_pow_of_prime hpz hxy hx (by exact_mod_cast hnd), hs', Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]`. Rewrite using `[Int.emultiplicity_pow_sub_pow hp (hp.odd_of_ne_two hl) hxy hx n, hs', Nat.factorization_def n hp, Nat.cast_add, padicValNat_eq_emultiplicity hn0]`. Rewrite `key` using `[one_pow]`. Introduce `h`.

Use `le_emultiplicity_of_pow_dvd h` as an intermediate fact. Rewrite `this` using `[key]`. Use `Nat.cast_le.1 this` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem nsa_lte (s n : ℕ) (hs : s ≠ 0) (hn : Odd n) :
    ¬ (l : ℤ) ^ (s + n.factorization l + 1) ∣ (1 + (l : ℤ) ^ s) ^ n - 1 := by
  have hp : l.Prime := Fact.out
  have hpz : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hxy : (l : ℤ) ∣ (1 + (l : ℤ) ^ s) - 1 := by
    simpa using dvd_pow_self (l : ℤ) hs
  have hx : ¬ (l : ℤ) ∣ 1 + (l : ℤ) ^ s := by
    intro h
    exact hpz.not_dvd_one ((dvd_add_left (dvd_pow_self (l : ℤ) hs)).1 h)
  have hs' : emultiplicity (l : ℤ) ((1 + (l : ℤ) ^ s) - 1) = s := by
    rw [add_sub_cancel_left]
    exact emultiplicity_pow_self_of_prime hpz s
  have key : emultiplicity (l : ℤ) ((1 + (l : ℤ) ^ s) ^ n - 1 ^ n) =
      ((s + n.factorization l : ℕ) : ℕ∞) := by
    by_cases hl : l = 2
    · have hnd : ¬ l ∣ n := by
        subst hl
        exact hn.not_two_dvd_nat
      rw [emultiplicity_pow_sub_pow_of_prime hpz hxy hx (by exact_mod_cast hnd), hs',
        Nat.factorization_eq_zero_of_not_dvd hnd, add_zero]
    · rw [Int.emultiplicity_pow_sub_pow hp (hp.odd_of_ne_two hl) hxy hx n, hs',
        Nat.factorization_def n hp, Nat.cast_add, padicValNat_eq_emultiplicity hn0]
  rw [one_pow] at key
  intro h
  have := le_emultiplicity_of_pow_dvd h
  rw [key] at this
  have := Nat.cast_le.1 this
  omega

/- English proof (translation)
Take `⟨g, hg⟩` from `h (m + 1)`. Use `Nat.sInf_le ⟨g, fun hc => hu ?_⟩` and prove the remaining obligations. Establish `h2` using `hg.trans (sub_dvd_pow_sub_pow ((ε g : ℤ_[l]ˣ) : ℤ_[l]) (u : ℤ_[l]) n)`. Establish `h3` using `dvd_sub hc h2`. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem nuOf_le_of_approx {Γ : Type} [Group Γ] (ε : Γ →* ℤ_[l]ˣ) (n m : ℕ) (u : ℤ_[l]ˣ)
    (h : ∀ k : ℕ, ∃ g, (l : ℤ_[l]) ^ k ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) - u)
    (hu : ¬ (l : ℤ_[l]) ^ (m + 1) ∣ (u : ℤ_[l]) ^ n - 1) : nuOf l ε n ≤ m := by
  obtain ⟨g, hg⟩ := h (m + 1)
  refine Nat.sInf_le ⟨g, fun hc => hu ?_⟩
  have h2 := hg.trans (sub_dvd_pow_sub_pow ((ε g : ℤ_[l]ˣ) : ℤ_[l]) (u : ℤ_[l]) n)
  have h3 := dvd_sub hc h2
  convert h3 using 1
  ring

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Distinguish the cases in `hlC : l ∣ C`. Rewrite using `[if_pos hlC]`. Establish `hs : C.factorization l ≠ 0` using `(hp.factorization_pos_of_dvd hC hlC).ne'`. Generalize the expression as in `C.factorization l = s at hs ⊢`.

Establish `hU : IsUnit (1 + (l : ℤ_[l]) ^ s)`. Apply `nsa_isUnit` to reduce the goal to its premises. Introduce `h`. Conclude with `PadicInt.prime_p.not_dvd_one ((dvd_add_left (dvd_pow_self (l : ℤ_[l]) hs)).1 h)`. Use `⟨hU.unit, by simp, fun h => nsa_lte l s n hs hn ?_⟩` and prove the remaining obligations.

Rewrite using `[← PadicInt.pow_p_dvd_int_iff]`. Simplify using `using h`. Rewrite using `[if_neg hlC, Nat.factorization_eq_zero_of_not_dvd hlC]`. Use `⟨-1, by simp, fun h => hlC ?_⟩` and prove the remaining obligations. Establish `e : ((-1 : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 = -((2 : ℕ) : ℤ_[l])`.

Simplify using `only [Units.val_neg, Units.val_one, hn.neg_one_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e, dvd_neg]`. Use `nsa_nat l _ _ h` as an intermediate fact.

Simplify using `only [add_zero, zero_add, pow_one] at this`. Conclude with `this.trans h2`.
-/
theorem exists_unit_not_dvd (C n : ℕ) (hC : C ≠ 0) (h2 : 2 ∣ C) (hn : Odd n) :
    ∃ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ C.factorization l ∣ (u : ℤ_[l]) - 1 ∧
      ¬ (l : ℤ_[l]) ^ (C.factorization l + (if l ∣ C then n.factorization l else 0) + 1) ∣ (u : ℤ_[l]) ^ n - 1 := by
  have hp : l.Prime := Fact.out
  by_cases hlC : l ∣ C
  · rw [if_pos hlC]
    have hs : C.factorization l ≠ 0 := (hp.factorization_pos_of_dvd hC hlC).ne'
    generalize C.factorization l = s at hs ⊢
    have hU : IsUnit (1 + (l : ℤ_[l]) ^ s) := by
      apply nsa_isUnit
      intro h
      exact PadicInt.prime_p.not_dvd_one ((dvd_add_left (dvd_pow_self (l : ℤ_[l]) hs)).1 h)
    refine ⟨hU.unit, by simp, fun h => nsa_lte l s n hs hn ?_⟩
    rw [← PadicInt.pow_p_dvd_int_iff]
    simpa using h
  · rw [if_neg hlC, Nat.factorization_eq_zero_of_not_dvd hlC]
    refine ⟨-1, by simp, fun h => hlC ?_⟩
    have e : ((-1 : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 = -((2 : ℕ) : ℤ_[l]) := by
      simp only [Units.val_neg, Units.val_one, hn.neg_one_pow]
      push_cast
      ring
    rw [e, dvd_neg] at h
    have := nsa_nat l _ _ h
    simp only [add_zero, zero_add, pow_one] at this
    exact this.trans h2

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Take `⟨g, hg⟩` from `IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)`. Rewrite `hg` using `[Nat.card_eq_fintype_card, ZMod.card_units]`. Establish `hx : PadicInt.toZMod ((((g : ZMod l).val : ℕ)) : ℤ_[l]) = (g : ZMod l)`. Rewrite using `[map_natCast, ZMod.natCast_zmod_val]`.

Establish `hU : IsUnit ((((g : ZMod l).val : ℕ)) : ℤ_[l])`. Apply `nsa_isUnit` to reduce the goal to its premises. Rewrite using `[nsa_dvd_iff, hx]`. Conclude with `g.ne_zero`. Use `⟨hU.unit, fun h => hn ?_⟩` and prove the remaining obligations.

Rewrite `h` using `[zero_add, pow_one, nsa_dvd_iff, map_sub, map_one, map_pow, Units.val_pow_eq_pow_val, map_pow, IsUnit.unit_spec, hx, sub_eq_zero, ← pow_mul]`. Establish `h1 : g ^ (2 * n) = 1`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `using h`. Establish `h2` using `orderOf_dvd_of_pow_eq_one h1`.

Rewrite `h2` using `[hg]`. Take `⟨k, hk⟩` from `hp.odd_of_ne_two hl`. Establish `e1 : l - 1 = 2 * k` using `by omega`. Rewrite `h2`, the goal using `[e1]`. Rewrite using `[Nat.mul_div_cancel_left k two_pos]`.

Conclude with `Nat.dvd_of_mul_dvd_mul_left two_pos h2`.
-/
theorem exists_sq_unit_not_dvd (n : ℕ) (hn : ¬ (l - 1) / 2 ∣ n) (hl : l ≠ 2) :
    ∃ u : ℤ_[l]ˣ, ¬ (l : ℤ_[l]) ^ (0 + 1) ∣ ((u ^ 2 : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by
  have hp : l.Prime := Fact.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  have hx : PadicInt.toZMod ((((g : ZMod l).val : ℕ)) : ℤ_[l]) = (g : ZMod l) := by
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hU : IsUnit ((((g : ZMod l).val : ℕ)) : ℤ_[l]) := by
    apply nsa_isUnit
    rw [nsa_dvd_iff, hx]
    exact g.ne_zero
  refine ⟨hU.unit, fun h => hn ?_⟩
  rw [zero_add, pow_one, nsa_dvd_iff, map_sub, map_one, map_pow, Units.val_pow_eq_pow_val, map_pow,
    IsUnit.unit_spec, hx, sub_eq_zero, ← pow_mul] at h
  have h1 : g ^ (2 * n) = 1 := by
    apply Units.ext
    simpa using h
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hg] at h2
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hl
  have e1 : l - 1 = 2 * k := by omega
  rw [e1] at h2 ⊢
  rw [Nat.mul_div_cancel_left k two_pos]
  exact Nat.dvd_of_mul_dvd_mul_left two_pos h2

end KStar.Tree
