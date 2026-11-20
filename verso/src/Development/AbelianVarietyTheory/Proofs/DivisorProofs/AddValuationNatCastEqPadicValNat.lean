import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `C _ _ v p hp hvp n hn`. Establish `h1 : v (1 : C) = 0` using `v.map_one`. Establish `hnat : ∀ m : ℕ, 0 ≤ v (m : C)`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `h` using `v.map_add (k : C) 1`. Rewrite `h` using `[h1]`. Use `push_cast`.

Conclude with `le_trans (le_min ih le_rfl) h`. Establish `hint : ∀ a : ℤ, 0 ≤ v (a : C)`. Introduce `a`. Take `⟨m, rfl | rfl⟩` from `a.eq_nat_or_neg`. Simplify using `using hnat m`.

Simplify `hnat m` using `[v.map_neg]`. Establish `hcop : ∀ m : ℕ, Nat.Coprime m p → v (m : C) = 0`. Introduce `m hm`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < v (m : C)` using `lt_of_le_of_ne (hnat m) (Ne.symm hne)`.

Establish `hbez : ((1 : ℤ)) = (m : ℤ) * Nat.gcdA m p + (p : ℤ) * Nat.gcdB m p`. Use `Nat.gcd_eq_gcd_ab m p` as an intermediate fact. Rewrite `this` using `[hm]`. Simplify using `using this`. Establish `hC : (1 : C) = (m : C) * ((Nat.gcdA m p : ℤ) : C) + (p : C) * ((Nat.gcdB m p : ℤ) : C)`.

Use `congrArg (fun z : ℤ => (z : C)) hbez` as an intermediate fact. Simplify using `using this`. Establish `ha : 0 < v ((m : C) * ((Nat.gcdA m p : ℤ) : C))`. Rewrite using `[v.map_mul]`. Conclude with `lt_of_lt_of_le hpos (le_add_of_nonneg_right (hint _))`.

Establish `hb : 0 < v ((p : C) * ((Nat.gcdB m p : ℤ) : C))`. Rewrite using `[v.map_mul, hvp]`. Conclude with `lt_of_lt_of_le (by exact_mod_cast zero_lt_one) (le_add_of_nonneg_right (hint _))`. Establish `h` using `v.map_add ((m : C) * ((Nat.gcdA m p : ℤ) : C)) ((p : C) * ((Nat.gcdB m p : ℤ) : C))`. Rewrite `h` using `[← hC, h1]`.

Conclude with `absurd (lt_of_lt_of_le (lt_min ha hb) h) (lt_irrefl _)`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Take `⟨m, hm⟩` from `pow_padicValNat_dvd (p := p) (n := n)`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hn (by simpa using hm)`. Establish `hnd : ¬ p ∣ m`. Introduce `hd`. Take `⟨c, rfl⟩` from `hd`. Establish `: p ^ (padicValNat p n + 1) ∣ n` using `⟨c, by rw [pow_succ, mul_assoc, ← hm]⟩`.

Conclude with `pow_succ_padicValNat_not_dvd hn this`. Establish `hcm : Nat.Coprime m p` using `((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm`. Establish `hcast : (n : C) = (p : C) ^ (padicValNat p n) * (m : C)` using `by conv_lhs => rw [hm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hcast, v.map_mul, v.map_pow, hvp, hcop m hcm, add_zero]`. Simplify using the standard rewrite rules.
-/
theorem addValuation_natCast_eq_padicValNat :
    ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime →
      v (p : C) = 1 → ∀ n : ℕ, n ≠ 0 →
        v (n : C) = (((padicValNat p n : ℕ) : ℝ) : WithTop ℝ) := by
  intro C _ _ v p hp hvp n hn
  have h1 : v (1 : C) = 0 := v.map_one

  have hnat : ∀ m : ℕ, 0 ≤ v (m : C) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      have h := v.map_add (k : C) 1
      rw [h1] at h
      push_cast
      exact le_trans (le_min ih le_rfl) h
  have hint : ∀ a : ℤ, 0 ≤ v (a : C) := by
    intro a
    obtain ⟨m, rfl | rfl⟩ := a.eq_nat_or_neg
    · simpa using hnat m
    · simpa [v.map_neg] using hnat m

  have hcop : ∀ m : ℕ, Nat.Coprime m p → v (m : C) = 0 := by
    intro m hm
    by_contra hne
    have hpos : 0 < v (m : C) := lt_of_le_of_ne (hnat m) (Ne.symm hne)
    have hbez : ((1 : ℤ)) = (m : ℤ) * Nat.gcdA m p + (p : ℤ) * Nat.gcdB m p := by
      have := Nat.gcd_eq_gcd_ab m p
      rw [hm] at this
      simpa using this
    have hC : (1 : C) = (m : C) * ((Nat.gcdA m p : ℤ) : C) + (p : C) * ((Nat.gcdB m p : ℤ) : C) := by
      have := congrArg (fun z : ℤ => (z : C)) hbez
      simpa using this
    have ha : 0 < v ((m : C) * ((Nat.gcdA m p : ℤ) : C)) := by
      rw [v.map_mul]
      exact lt_of_lt_of_le hpos (le_add_of_nonneg_right (hint _))
    have hb : 0 < v ((p : C) * ((Nat.gcdB m p : ℤ) : C)) := by
      rw [v.map_mul, hvp]
      exact lt_of_lt_of_le (by exact_mod_cast zero_lt_one) (le_add_of_nonneg_right (hint _))
    have h := v.map_add ((m : C) * ((Nat.gcdA m p : ℤ) : C)) ((p : C) * ((Nat.gcdB m p : ℤ) : C))
    rw [← hC, h1] at h
    exact absurd (lt_of_lt_of_le (lt_min ha hb) h) (lt_irrefl _)

  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := pow_padicValNat_dvd (p := p) (n := n)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hn (by simpa using hm)
  have hnd : ¬ p ∣ m := by
    intro hd
    obtain ⟨c, rfl⟩ := hd
    have : p ^ (padicValNat p n + 1) ∣ n := ⟨c, by rw [pow_succ, mul_assoc, ← hm]⟩
    exact pow_succ_padicValNat_not_dvd hn this
  have hcm : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
  have hcast : (n : C) = (p : C) ^ (padicValNat p n) * (m : C) := by
    conv_lhs => rw [hm]
    push_cast
    ring
  rw [hcast, v.map_mul, v.map_pow, hvp, hcop m hcm, add_zero]
  simp

end GlobalTheory
