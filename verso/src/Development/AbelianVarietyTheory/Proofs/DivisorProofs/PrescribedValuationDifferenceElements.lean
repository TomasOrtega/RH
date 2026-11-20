import Mathlib

open IsDedekindDomain WithZero

namespace GlobalTheory

/- English proof (translation)
Establish `hm : P ∈ nonZeroDivisors (Ideal A)` using `mem_nonZeroDivisors_of_ne_zero hP`. Establish `hm' : P ^ Nat.card (ClassGroup A) ∈ nonZeroDivisors (Ideal A)` using `pow_mem hm _`. Establish `h1 : ClassGroup.mk0 (⟨_, hm'⟩ : nonZeroDivisors (Ideal A)) = 1`. Establish `: (⟨_, hm'⟩ : nonZeroDivisors (Ideal A)) = (⟨P, hm⟩ : nonZeroDivisors (Ideal A)) ^ Nat.card (ClassGroup A)` using `Subtype.ext rfl`. Rewrite using `[this, map_pow]`.

Conclude with `pow_card_eq_one'`. Take `⟨x, hx⟩` from `((ClassGroup.mk0_eq_one_iff hm').1 h1).principal`. Conclude with `⟨x, hx⟩`.
-/
theorem exists_span_eq_pow_card_classGroup {A : Type} [CommRing A] [IsDedekindDomain A]
    [Finite (ClassGroup A)] (P : Ideal A) (hP : P ≠ ⊥) :
    ∃ x : A, P ^ Nat.card (ClassGroup A) = Ideal.span {x} := by
  have hm : P ∈ nonZeroDivisors (Ideal A) := mem_nonZeroDivisors_of_ne_zero hP
  have hm' : P ^ Nat.card (ClassGroup A) ∈ nonZeroDivisors (Ideal A) := pow_mem hm _
  have h1 : ClassGroup.mk0 (⟨_, hm'⟩ : nonZeroDivisors (Ideal A)) = 1 := by
    have : (⟨_, hm'⟩ : nonZeroDivisors (Ideal A)) =
        (⟨P, hm⟩ : nonZeroDivisors (Ideal A)) ^ Nat.card (ClassGroup A) := Subtype.ext rfl
    rw [this, map_pow]; exact pow_card_eq_one'
  obtain ⟨x, hx⟩ := ((ClassGroup.mk0_eq_one_iff hm').1 h1).principal
  exact ⟨x, hx⟩

/- English proof (translation)
Establish `: P ^ k ≠ ⊥`. Rewrite using `[← Ideal.zero_eq_bot]; exact pow_ne_zero _ (by rwa [Ideal.zero_eq_bot])`. Rewrite `this` using `[hx, Ne, Ideal.span_singleton_eq_bot]`. Then use the resulting hypothesis.
-/
theorem ne_zero_of_pow_eq_span {A : Type} [CommRing A] [IsDedekindDomain A]
    (P : Ideal A) (hP : P ≠ ⊥) (k : ℕ) (x : A) (hx : P ^ k = Ideal.span {x}) : x ≠ 0 := by
  have : P ^ k ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]; exact pow_ne_zero _ (by rwa [Ideal.zero_eq_bot])
  rwa [hx, Ne, Ideal.span_singleton_eq_bot] at this

/- English proof (translation)
Establish `hx0` using `ne_zero_of_pow_eq_span P hP k x hx`. Rewrite using `[v.intValuation_eq_exp_neg_multiplicity hx0, ← hx]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[multiplicity_pow_self_of_prime v.prime]`.

Establish `: multiplicity v.asIdeal (P ^ k) = 0`. Rewrite using `[multiplicity_eq_zero]`. Introduce `hd`. Establish `hle : P ^ k ≤ v.asIdeal` using `Ideal.le_of_dvd hd`. Establish `hPv : P ≤ v.asIdeal` using `v.isPrime.le_of_pow_le hle`.

Conclude with `h ((hPp.isMaximal hP).eq_of_le v.isPrime.ne_top hPv).symm`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem intValuation_of_pow_eq_span {A : Type} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) (P : Ideal A) [hPp : P.IsPrime] (hP : P ≠ ⊥) (k : ℕ) (x : A)
    (hx : P ^ k = Ideal.span {x}) :
    v.intValuation x = if v.asIdeal = P then exp (-(k : ℤ)) else 1 := by
  have hx0 := ne_zero_of_pow_eq_span P hP k x hx
  rw [v.intValuation_eq_exp_neg_multiplicity hx0, ← hx]
  split_ifs with h
  · subst h
    rw [multiplicity_pow_self_of_prime v.prime]
  · have : multiplicity v.asIdeal (P ^ k) = 0 := by
      rw [multiplicity_eq_zero]
      intro hd
      have hle : P ^ k ≤ v.asIdeal := Ideal.le_of_dvd hd
      have hPv : P ≤ v.asIdeal := v.isPrime.le_of_pow_le hle
      exact h ((hPp.isMaximal hP).eq_of_le v.isPrime.ne_top hPv).symm
    rw [this]; simp

/- English proof (translation)
Use `⟨(v.intValuation_le_pow_iff_mem x k).1 h.le, fun hm => ?_⟩` and prove the remaining obligations. Use `(v.intValuation_le_pow_iff_mem x (k + 1)).2 hm` as an intermediate fact. Rewrite `this` using `[h, exp_le_exp]`. Move the coercions through the operations in `at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_pow_of_intValuation_eq {A : Type} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) (x : A) (k : ℕ) (h : v.intValuation x = exp (-(k : ℤ))) :
    x ∈ v.asIdeal ^ k ∧ x ∉ v.asIdeal ^ (k + 1) := by
  refine ⟨(v.intValuation_le_pow_iff_mem x k).1 h.le, fun hm => ?_⟩
  have := (v.intValuation_le_pow_iff_mem x (k + 1)).2 hm
  rw [h, exp_le_exp] at this
  push_cast at this; omega

/- English proof (translation)
Introduce `A _ _ _ S q`. Use `set h := Nat.card (ClassGroup A) with hh`. Establish `hpos : 0 < h` using `Nat.card_pos`. Use `set d : ℕ := ∏ P ∈ S, (q P).den with hd`. Establish `dpos : 0 < d` using `Finset.prod_pos fun P _ => (q P).den_pos`.

Establish `hint : ∀ P, ∃ z : ℤ, P ∈ S → (d : ℚ) * q P = z`. Introduce `P`. Distinguish the cases in `hP : P ∈ S`. Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem (fun P => (q P).den) hP`. Use `⟨(k : ℤ) * (q P).num, fun _ => ?_⟩` and prove the remaining obligations.

Establish `hk' : (d : ℚ) = (q P).den * k` using `by exact_mod_cast hk`. Establish `e` using `Rat.mul_den_eq_num (q P)`. Rewrite using `[hk']`. Use `push_cast`. Rewrite using `[← e]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨0, fun h' => absurd h' hP⟩`. Use `choose n hn using hint`. Establish `hgen : ∀ P : Ideal A, ∃ x : A, P ≠ ⊥ → P ^ h = Ideal.span {x}`. Introduce `P`.

Distinguish the cases in `hP : P = ⊥`. Conclude with `⟨0, fun h' => absurd hP h'⟩`. Take `⟨x, hx⟩` from `exists_span_eq_pow_card_classGroup P hP`. Conclude with `⟨x, fun _ => hx⟩`. Use `choose g hg using hgen`.

Use `set S' := S.filter (fun P => P.IsPrime ∧ P ≠ ⊥) with hS'`. Establish `hval : ∀ (v : HeightOneSpectrum A) (e : Ideal A → ℕ), v.intValuation (∏ P ∈ S', g P ^ e P) = if v.asIdeal ∈ S' then exp (-((h * e v.asIdeal : ℕ) : ℤ)) else 1`. Introduce `v e`. Rewrite using `[map_prod]`. Establish `: ∀ P ∈ S', v.intValuation (g P ^ e P) = if v.asIdeal = P then exp (-((h * e v.asIdeal : ℕ) : ℤ)) else 1`.

Introduce `P hP`. Take `⟨_, hP1, hP2⟩` from `Finset.mem_filter.1 hP`. Use `haveI := hP1`. Rewrite using `[map_pow, intValuation_of_pow_eq_span v P hP2 h (g P) (hg P hP2)]`. Use `split_ifs with hv`.

Substitute `hv` using the available equality. Rewrite using `[← exp_nsmul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Rewrite using `[Finset.prod_congr rfl this, Finset.prod_ite_eq]`. Establish `hne : ∀ e : Ideal A → ℕ, (∏ P ∈ S', g P ^ e P) ≠ 0`. Introduce `e`. Use `Finset.prod_ne_zero_iff.2 fun P hP => pow_ne_zero _ ?_` and prove the remaining obligations.

Take `⟨_, _, hP2⟩` from `Finset.mem_filter.1 hP`. Conclude with `ne_zero_of_pow_eq_span P hP2 h (g P) (hg P hP2)`. Use `⟨d * h, ∏ P ∈ S', g P ^ (n P).toNat, ∏ P ∈ S', g P ^ (-n P).toNat, Nat.mul_pos dpos hpos, hne _, hne _, ?_⟩` and prove the remaining obligations. Introduce `P hP hPb`. Set `v : HeightOneSpectrum A` to `⟨P, hP, hPb⟩`.

Distinguish the cases in `hS : P ∈ S`. Establish `hS'm : P ∈ S'` using `Finset.mem_filter.2 ⟨hS, hP, hPb⟩`. Establish `ha` using `mem_pow_of_intValuation_eq v _ _ ((hval v (fun P => (n P).toNat)).trans (if_pos hS'm))`. Establish `hb` using `mem_pow_of_intValuation_eq v _ _ ((hval v (fun P => (-n P).toNat)).trans (if_pos hS'm))`. Use `⟨h * (n P).toNat, h * (-n P).toNat, ha.1, ha.2, hb.1, hb.2, ?_⟩` and prove the remaining obligations.

Rewrite using `[if_pos hS]`. Establish `key' : (((n P).toNat : ℕ) : ℚ) - (((-n P).toNat : ℕ) : ℚ) = (n P : ℚ)`. Conclude with `Int.toNat_sub_toNat_neg (n P)` after adjusting the coercions. Rewrite using `[Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, ← mul_sub, key', ← hn P hS]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hS'm : P ∉ S'` using `fun hm => hS (Finset.mem_filter.1 hm).1`. Establish `h1 : ∀ e : Ideal A → ℕ, v.intValuation (∏ P ∈ S', g P ^ e P) = exp (-((0 : ℕ) : ℤ))`. Introduce `e`. Rewrite using `[hval v e, if_neg hS'm]`. Simplify using the standard rewrite rules.

Establish `ha` using `mem_pow_of_intValuation_eq v _ _ (h1 (fun P => (n P).toNat))`. Establish `hb` using `mem_pow_of_intValuation_eq v _ _ (h1 (fun P => (-n P).toNat))`. Conclude with `⟨0, 0, ha.1, ha.2, hb.1, hb.2, by simp [hS]⟩`.
-/
theorem exists_num_den_of_rat_divisor : ∀ (A : Type) [CommRing A] [IsDedekindDomain A] [Finite (ClassGroup A)] (S : Finset (Ideal A))
    (q : Ideal A → ℚ), ∃ (m : ℕ) (a b : A), 0 < m ∧ a ≠ 0 ∧ b ≠ 0 ∧ ∀ P : Ideal A, P.IsPrime → P ≠ ⊥ →
      ∃ na nb : ℕ, a ∈ P ^ na ∧ a ∉ P ^ (na + 1) ∧ b ∈ P ^ nb ∧ b ∉ P ^ (nb + 1) ∧
        ((na : ℚ) - nb = (m : ℚ) * (if P ∈ S then q P else 0)) := by
  intro A _ _ _ S q
  classical
  set h := Nat.card (ClassGroup A) with hh
  have hpos : 0 < h := Nat.card_pos
  set d : ℕ := ∏ P ∈ S, (q P).den with hd
  have dpos : 0 < d := Finset.prod_pos fun P _ => (q P).den_pos
  have hint : ∀ P, ∃ z : ℤ, P ∈ S → (d : ℚ) * q P = z := by
    intro P
    by_cases hP : P ∈ S
    · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun P => (q P).den) hP
      refine ⟨(k : ℤ) * (q P).num, fun _ => ?_⟩
      have hk' : (d : ℚ) = (q P).den * k := by exact_mod_cast hk
      have e := Rat.mul_den_eq_num (q P)
      rw [hk']; push_cast; rw [← e]; ring
    · exact ⟨0, fun h' => absurd h' hP⟩
  choose n hn using hint
  have hgen : ∀ P : Ideal A, ∃ x : A, P ≠ ⊥ → P ^ h = Ideal.span {x} := by
    intro P
    by_cases hP : P = ⊥
    · exact ⟨0, fun h' => absurd hP h'⟩
    · obtain ⟨x, hx⟩ := exists_span_eq_pow_card_classGroup P hP
      exact ⟨x, fun _ => hx⟩
  choose g hg using hgen
  set S' := S.filter (fun P => P.IsPrime ∧ P ≠ ⊥) with hS'
  have hval : ∀ (v : HeightOneSpectrum A) (e : Ideal A → ℕ),
      v.intValuation (∏ P ∈ S', g P ^ e P) =
        if v.asIdeal ∈ S' then exp (-((h * e v.asIdeal : ℕ) : ℤ)) else 1 := by
    intro v e
    rw [map_prod]
    have : ∀ P ∈ S', v.intValuation (g P ^ e P) =
        if v.asIdeal = P then exp (-((h * e v.asIdeal : ℕ) : ℤ)) else 1 := by
      intro P hP
      obtain ⟨_, hP1, hP2⟩ := Finset.mem_filter.1 hP
      haveI := hP1
      rw [map_pow, intValuation_of_pow_eq_span v P hP2 h (g P) (hg P hP2)]
      split_ifs with hv
      · subst hv; rw [← exp_nsmul]; congr 1; push_cast; ring
      · simp
    rw [Finset.prod_congr rfl this, Finset.prod_ite_eq]
  have hne : ∀ e : Ideal A → ℕ, (∏ P ∈ S', g P ^ e P) ≠ 0 := by
    intro e
    refine Finset.prod_ne_zero_iff.2 fun P hP => pow_ne_zero _ ?_
    obtain ⟨_, _, hP2⟩ := Finset.mem_filter.1 hP
    exact ne_zero_of_pow_eq_span P hP2 h (g P) (hg P hP2)
  refine ⟨d * h, ∏ P ∈ S', g P ^ (n P).toNat, ∏ P ∈ S', g P ^ (-n P).toNat,
    Nat.mul_pos dpos hpos, hne _, hne _, ?_⟩
  intro P hP hPb
  let v : HeightOneSpectrum A := ⟨P, hP, hPb⟩
  by_cases hS : P ∈ S
  · have hS'm : P ∈ S' := Finset.mem_filter.2 ⟨hS, hP, hPb⟩
    have ha := mem_pow_of_intValuation_eq v _ _ ((hval v (fun P => (n P).toNat)).trans (if_pos hS'm))
    have hb := mem_pow_of_intValuation_eq v _ _ ((hval v (fun P => (-n P).toNat)).trans (if_pos hS'm))
    refine ⟨h * (n P).toNat, h * (-n P).toNat, ha.1, ha.2, hb.1, hb.2, ?_⟩
    rw [if_pos hS]
    have key' : (((n P).toNat : ℕ) : ℚ) - (((-n P).toNat : ℕ) : ℚ) = (n P : ℚ) := by
      exact_mod_cast Int.toNat_sub_toNat_neg (n P)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, ← mul_sub, key', ← hn P hS]
    ring
  · have hS'm : P ∉ S' := fun hm => hS (Finset.mem_filter.1 hm).1
    have h1 : ∀ e : Ideal A → ℕ, v.intValuation (∏ P ∈ S', g P ^ e P) = exp (-((0 : ℕ) : ℤ)) := by
      intro e
      rw [hval v e, if_neg hS'm]; simp
    have ha := mem_pow_of_intValuation_eq v _ _ (h1 (fun P => (n P).toNat))
    have hb := mem_pow_of_intValuation_eq v _ _ (h1 (fun P => (-n P).toNat))
    exact ⟨0, 0, ha.1, ha.2, hb.1, hb.2, by simp [hS]⟩

end GlobalTheory
