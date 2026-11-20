import Mathlib

namespace ReciprocityTheory.ChartRestriction.L1

open scoped NumberTheorySymbols

/- English proof (translation)
Take `⟨d', rfl⟩` from `h3`. Establish `hd'4 : d' % 4 = 1` using `by omega`. Establish `hd'1 : d' ≠ 1`. Introduce and unpack `rfl`. Conclude with `hd3 rfl`.

Take `⟨q, hq, hqd⟩` from `Nat.exists_prime_and_dvd hd'1`. Establish `hq2 : q ≠ 2`. Introduce and unpack `rfl`. Take `⟨t, ht⟩` from `hqd`. Use linear arithmetic over natural numbers and integers.

Use `haveI := Fact.mk hq`. Take `⟨c, hc⟩` from `FiniteField.exists_nonsquare (F := ZMod q) (by rw [ZMod.ringChar_zmod_n]; exact hq2)`. Take `⟨d'', rfl⟩` from `hqd`. Establish `hd''0 : d'' ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hd4`. Use `haveI : NeZero d'' := ⟨hd''0⟩`. Use `haveI : NeZero q := ⟨hq.ne_zero⟩`. Establish `hcop1 : Nat.Coprime q d''`. Use `(Nat.Prime.coprime_iff_not_dvd hq).mpr ?_` and prove the remaining obligations.

Introduce and unpack `⟨e, rfl⟩`. Conclude with `absurd (Nat.isUnit_iff.mp (hsq q ⟨3 * e, by ring⟩)) hq.one_lt.ne'`. Establish `hcop2 : Nat.Coprime 3 (q * d'')`. Use `(Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_` and prove the remaining obligations. Introduce and unpack `⟨e, he⟩`.

Conclude with `absurd (Nat.isUnit_iff.mp (hsq 3 ⟨e, by rw [he]; ring⟩)) (by norm_num)`. Take `⟨b, hb1, hb2⟩` from `Nat.chineseRemainder hcop1 c.val 1`. Take `⟨a, ha1, ha2⟩` from `Nat.chineseRemainder hcop2 2 b`. Use `⟨a, ?_, ?_⟩` and prove the remaining obligations. Unfold `Nat.ModEq at ha1`.

Use linear arithmetic over natural numbers and integers. Establish `hmq : a % q = c.val % q` using `(ha2.of_mul_right d'').trans hb1`. Establish `hmd : a % d'' = 1 % d''` using `(ha2.of_mul_left q).trans hb2`. Establish `hm3 : a % 3 = 2`. Unfold `Nat.ModEq at ha1`.

Use linear arithmetic over natural numbers and integers. Establish `hJ3 : J((a : ℤ) | 3) = -1`. Rewrite using `[jacobiSym.mod_left]`. Establish `: (a : ℤ) % ((3 : ℕ) : ℤ) = 2` using `by omega`. Rewrite using `[this]`.

Evaluate the numerical expressions. Establish `hJq : J((a : ℤ) | q) = -1`. Establish `: (a : ℤ) % (q : ℤ) = (c.val : ℤ) % (q : ℤ)` using `by exact_mod_cast hmq`. Rewrite using `[jacobiSym.mod_left, this, ← jacobiSym.mod_left, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]`. Simplify using `using hc`.

Establish `hJd : J((a : ℤ) | d'') = 1`. Establish `: (a : ℤ) % (d'' : ℤ) = ((1 : ℕ) : ℤ) % (d'' : ℤ)` using `by exact_mod_cast hmd`. Rewrite using `[jacobiSym.mod_left, this, ← jacobiSym.mod_left, Nat.cast_one, jacobiSym.one_left]`. Rewrite using `[jacobiSym.mul_right, jacobiSym.mul_right, hJ3, hJq, hJd]`. Evaluate the numerical expressions.
-/
theorem prime_choice_class (d : ℕ) (hsq : Squarefree d) (hd4 : d % 4 = 3) (h3 : 3 ∣ d) (hd3 : d ≠ 3) :
    ∃ a : ℕ, a % 3 = 2 ∧ J((a : ℤ) | d) = 1 := by
  obtain ⟨d', rfl⟩ := h3
  have hd'4 : d' % 4 = 1 := by omega
  have hd'1 : d' ≠ 1 := by
    rintro rfl
    exact hd3 rfl
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hd'1
  have hq2 : q ≠ 2 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hqd
    omega
  haveI := Fact.mk hq
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare (F := ZMod q) (by rw [ZMod.ringChar_zmod_n]; exact hq2)
  obtain ⟨d'', rfl⟩ := hqd
  have hd''0 : d'' ≠ 0 := by
    rintro rfl
    simp at hd4
  haveI : NeZero d'' := ⟨hd''0⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hcop1 : Nat.Coprime q d'' := by
    refine (Nat.Prime.coprime_iff_not_dvd hq).mpr ?_
    rintro ⟨e, rfl⟩
    exact absurd (Nat.isUnit_iff.mp (hsq q ⟨3 * e, by ring⟩)) hq.one_lt.ne'
  have hcop2 : Nat.Coprime 3 (q * d'') := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_
    rintro ⟨e, he⟩
    exact absurd (Nat.isUnit_iff.mp (hsq 3 ⟨e, by rw [he]; ring⟩)) (by norm_num)

  obtain ⟨b, hb1, hb2⟩ := Nat.chineseRemainder hcop1 c.val 1
  obtain ⟨a, ha1, ha2⟩ := Nat.chineseRemainder hcop2 2 b
  refine ⟨a, ?_, ?_⟩
  · unfold Nat.ModEq at ha1
    omega
  have hmq : a % q = c.val % q := (ha2.of_mul_right d'').trans hb1
  have hmd : a % d'' = 1 % d'' := (ha2.of_mul_left q).trans hb2
  have hm3 : a % 3 = 2 := by
    unfold Nat.ModEq at ha1
    omega
  have hJ3 : J((a : ℤ) | 3) = -1 := by
    rw [jacobiSym.mod_left]
    have : (a : ℤ) % ((3 : ℕ) : ℤ) = 2 := by omega
    rw [this]
    norm_num
  have hJq : J((a : ℤ) | q) = -1 := by
    have : (a : ℤ) % (q : ℤ) = (c.val : ℤ) % (q : ℤ) := by exact_mod_cast hmq
    rw [jacobiSym.mod_left, this, ← jacobiSym.mod_left, ← jacobiSym.legendreSym.to_jacobiSym,
      legendreSym.eq_neg_one_iff]
    simpa using hc
  have hJd : J((a : ℤ) | d'') = 1 := by
    have : (a : ℤ) % (d'' : ℤ) = ((1 : ℕ) : ℤ) % (d'' : ℤ) := by exact_mod_cast hmd
    rw [jacobiSym.mod_left, this, ← jacobiSym.mod_left, Nat.cast_one, jacobiSym.one_left]
  rw [jacobiSym.mul_right, jacobiSym.mul_right, hJ3, hJq, hJd]
  norm_num

/- English proof (translation)
Establish `hd : Odd d` using `Nat.odd_iff.mpr (by omega)`. Rewrite using `[jacobiSym.neg _ hp]`. Break down `Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hp) with h | h` into its components or cases. Rewrite using `[ZMod.χ₄_nat_one_mod_four h, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h hd]`. Rewrite using `[ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four hd4 h]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem prime_choice_recip (d p : ℕ) (hd4 : d % 4 = 3) (hp : Odd p) :
    J(-(d : ℤ) | p) = J((p : ℤ) | d) := by
  have hd : Odd d := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hp]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hp) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h hd]
  · rw [ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four hd4 h]
    ring

/- English proof (translation)
Establish `hpodd : Odd p` using `hp.odd_of_ne_two hp2`. Choose the witnesses or unpack the hypotheses as in `⟨r0, hr0e, hr0⟩ : ∃ r0 : ℕ, Even r0 ∧ p ∣ r0 ^ 2 + d := by`. Break down `Nat.even_or_odd s with he | ho` into its components or cases. Conclude with `⟨s, he, hs⟩`. Use `⟨s + p, ho.add_odd hpodd, ?_⟩` and prove the remaining obligations.

Establish `e : (s + p) ^ 2 + d = (s ^ 2 + d) + p * (2 * s + p)` using `by ring`. Rewrite using `[e]`. Conclude with `dvd_add hs (dvd_mul_right _ _)`. Establish `hndvd : ¬ p ∣ r0`. Introduce `h`.

Establish `h2 : p ∣ r0 ^ 2` using `dvd_pow h two_ne_zero`. Establish `hpd : p ∣ d` using `(Nat.dvd_add_right h2).mp hr0`. Use `Nat.le_of_dvd hd0 hpd` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hsq : p ^ 2 ∣ r0 ^ 2 + d`.

Use `⟨r0 + 2 * p, hr0e.add (even_two_mul p), ?_, ?_⟩` and prove the remaining obligations. Establish `e : (r0 + 2 * p) ^ 2 + d = (r0 ^ 2 + d) + p * (4 * r0 + 4 * p)` using `by ring`. Rewrite using `[e]`. Conclude with `dvd_add hr0 (dvd_mul_right _ _)`. Introduce `h`.

Establish `e : (r0 + 2 * p) ^ 2 + d = (r0 ^ 2 + d) + p ^ 2 * 4 + p * (4 * r0)` using `by ring`. Rewrite `h` using `[e]`. Establish `h1 : p ^ 2 ∣ p * (4 * r0)` using `(Nat.dvd_add_right (dvd_add hsq (dvd_mul_right _ _))).mp h`. Rewrite `h1` using `[pow_two]`. Establish `h2 : p ∣ 4 * r0` using `Nat.dvd_of_mul_dvd_mul_left hp.pos h1`.

Break down `(Nat.Prime.dvd_mul hp).mp h2 with h4 | h4` into its components or cases. Conclude with `hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)))`. Conclude with `hndvd h4`. Conclude with `⟨r0, hr0e, hr0, hsq⟩`.
-/
theorem prime_choice_lift (d p s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hd0 : 0 < d) (hdp : d < p)
    (hs : p ∣ s ^ 2 + d) : ∃ r : ℕ, Even r ∧ p ∣ r ^ 2 + d ∧ ¬ p ^ 2 ∣ r ^ 2 + d := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨r0, hr0e, hr0⟩ : ∃ r0 : ℕ, Even r0 ∧ p ∣ r0 ^ 2 + d := by
    rcases Nat.even_or_odd s with he | ho
    · exact ⟨s, he, hs⟩
    · refine ⟨s + p, ho.add_odd hpodd, ?_⟩
      have e : (s + p) ^ 2 + d = (s ^ 2 + d) + p * (2 * s + p) := by ring
      rw [e]
      exact dvd_add hs (dvd_mul_right _ _)
  have hndvd : ¬ p ∣ r0 := by
    intro h
    have h2 : p ∣ r0 ^ 2 := dvd_pow h two_ne_zero
    have hpd : p ∣ d := (Nat.dvd_add_right h2).mp hr0
    have := Nat.le_of_dvd hd0 hpd
    omega
  by_cases hsq : p ^ 2 ∣ r0 ^ 2 + d
  ·
    refine ⟨r0 + 2 * p, hr0e.add (even_two_mul p), ?_, ?_⟩
    · have e : (r0 + 2 * p) ^ 2 + d = (r0 ^ 2 + d) + p * (4 * r0 + 4 * p) := by ring
      rw [e]
      exact dvd_add hr0 (dvd_mul_right _ _)
    · intro h
      have e : (r0 + 2 * p) ^ 2 + d = (r0 ^ 2 + d) + p ^ 2 * 4 + p * (4 * r0) := by ring
      rw [e] at h
      have h1 : p ^ 2 ∣ p * (4 * r0) := (Nat.dvd_add_right (dvd_add hsq (dvd_mul_right _ _))).mp h
      rw [pow_two] at h1
      have h2 : p ∣ 4 * r0 := Nat.dvd_of_mul_dvd_mul_left hp.pos h1
      rcases (Nat.Prime.dvd_mul hp).mp h2 with h4 | h4
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)))
      · exact hndvd h4
  · exact ⟨r0, hr0e, hr0, hsq⟩

/- English proof (translation)
Take `⟨a, ha3, ha⟩` from `prime_choice_class d hsq hd4 h3 hd3`. Establish `hd0 : d ≠ 0` using `by omega`. Use `haveI : NeZero d := ⟨hd0⟩`. Establish `hunit : IsUnit (a : ZMod d)`. Rewrite using `[ZMod.isUnit_iff_coprime]`.

Assume the negation of the conclusion as `hnc`. Establish `h0 : J((a : ℤ) | d) = 0` using `jacobiSym.eq_zero_iff.mpr ⟨hd0, by simpa [Int.gcd_natCast_natCast] using hnc⟩`. Rewrite `h0` using `[ha]`. Conclude with `one_ne_zero h0`. Take `⟨p, hpgt, hp, hpa⟩` from `Nat.forall_exists_prime_gt_and_eq_mod hunit (b + d)`.

Establish `hpd : p % d = a % d` using `(ZMod.natCast_eq_natCast_iff' p a d).mp hpa`. Establish `hp3 : p % 3 = 2`. Rewrite using `[← Nat.mod_mod_of_dvd p h3, hpd, Nat.mod_mod_of_dvd a h3, ha3]`. Establish `hpodd : Odd p` using `hp.odd_of_ne_two (by omega)`. Establish `hmod : (p : ℤ) % (d : ℤ) = (a : ℤ) % (d : ℤ)` using `by exact_mod_cast hpd`.

Establish `hJ : J(-(d : ℤ) | p) = 1`. Rewrite using `[prime_choice_recip d p hd4 hpodd, jacobiSym.mod_left, hmod, ← jacobiSym.mod_left, ha]`. Use `haveI := Fact.mk hp`. Establish `hne : (((-(d : ℤ)) : ℤ) : ZMod p) ≠ 0`. Introduce `h0`.

Establish `h1 : (d : ZMod p) = 0`. Move the coercions through the operations in `at h0`. Simplify using `using h0`. Use `Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff d p).mp h1)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite `hJ` using `[← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p hne]`. Take `⟨x, hx⟩` from `hJ`. Establish `hs : p ∣ x.val ^ 2 + d`. Rewrite using `[← ZMod.natCast_eq_zero_iff]`. Move the coercions through the operations in `at hx ⊢`.

Rewrite using `[ZMod.natCast_zmod_val]`. Take the linear combination `-hx`. Take `⟨r, hr1, hr2, hr3⟩` from `prime_choice_lift d p x.val hp (by omega) (by omega) (by omega) hs`. Conclude with `⟨p, r, hp, by omega, by omega, hp3, hr1, hr2, hr3⟩`.
-/
theorem prime_choice (d b : ℕ) (hsq : Squarefree d) (hd4 : d % 4 = 3) (h3 : 3 ∣ d) (hd3 : d ≠ 3) :
    ∃ p r : ℕ, p.Prime ∧ b < p ∧ d < p ∧ p % 3 = 2 ∧ Even r ∧ p ∣ r ^ 2 + d ∧ ¬ p ^ 2 ∣ r ^ 2 + d := by
  obtain ⟨a, ha3, ha⟩ := prime_choice_class d hsq hd4 h3 hd3
  have hd0 : d ≠ 0 := by omega
  haveI : NeZero d := ⟨hd0⟩
  have hunit : IsUnit (a : ZMod d) := by
    rw [ZMod.isUnit_iff_coprime]
    by_contra hnc
    have h0 : J((a : ℤ) | d) = 0 := jacobiSym.eq_zero_iff.mpr ⟨hd0, by simpa [Int.gcd_natCast_natCast] using hnc⟩
    rw [ha] at h0
    exact one_ne_zero h0
  obtain ⟨p, hpgt, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (b + d)
  have hpd : p % d = a % d := (ZMod.natCast_eq_natCast_iff' p a d).mp hpa
  have hp3 : p % 3 = 2 := by
    rw [← Nat.mod_mod_of_dvd p h3, hpd, Nat.mod_mod_of_dvd a h3, ha3]
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hmod : (p : ℤ) % (d : ℤ) = (a : ℤ) % (d : ℤ) := by exact_mod_cast hpd
  have hJ : J(-(d : ℤ) | p) = 1 := by
    rw [prime_choice_recip d p hd4 hpodd, jacobiSym.mod_left, hmod, ← jacobiSym.mod_left, ha]
  haveI := Fact.mk hp
  have hne : (((-(d : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have h1 : (d : ZMod p) = 0 := by
      push_cast at h0
      simpa using h0
    have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff d p).mp h1)
    omega
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p hne] at hJ
  obtain ⟨x, hx⟩ := hJ
  have hs : p ∣ x.val ^ 2 + d := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast at hx ⊢
    rw [ZMod.natCast_zmod_val]
    linear_combination -hx
  obtain ⟨r, hr1, hr2, hr3⟩ := prime_choice_lift d p x.val hp (by omega) (by omega) (by omega) hs
  exact ⟨p, r, hp, by omega, by omega, hp3, hr1, hr2, hr3⟩

end ReciprocityTheory.ChartRestriction.L1
