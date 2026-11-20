import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ArtinMapSecondEqJacobiSym

noncomputable section

namespace Formalism.HC.D7

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

/- English proof (translation)
Rewrite using `[jacobiSym.mod_left, jacobiSym.mod_left (y : ℤ)]`. Use `congr 1`. Establish `h : ((x % p : ℕ) : ℤ) = ((y % p : ℕ) : ℤ)` using `congrArg _ hxy`. Simplify `h` using `[Int.natCast_mod]`.
-/
theorem jac_congr {x y p : ℕ} (hxy : x ≡ y [MOD p]) : jacobiSym (x : ℤ) p = jacobiSym (y : ℤ) p := by
  rw [jacobiSym.mod_left, jacobiSym.mod_left (y : ℤ)]
  congr 1
  have h : ((x % p : ℕ) : ℤ) = ((y % p : ℕ) : ℤ) := congrArg _ hxy
  simpa [Int.natCast_mod] using h

/- English proof (translation)
Establish `hp' : Odd p` using `Nat.odd_iff.mpr hp`. Establish `hr' : Odd r` using `Nat.odd_iff.mpr (by omega)`. Rewrite using `[jacobiSym.neg _ hp']`. Break down `(show p % 4 = 1 ∨ p % 4 = 3 by omega) with h4 | h4` into its components or cases. Rewrite using `[ZMod.χ₄_nat_one_mod_four h4, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h4 hr']`.

Rewrite using `[ZMod.χ₄_nat_three_mod_four h4, jacobiSym.quadratic_reciprocity_three_mod_four hr h4]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jac_recip {r p : ℕ} (hr : r % 4 = 3) (hp : p % 2 = 1) : jacobiSym (-(r : ℤ)) p = jacobiSym (p : ℤ) r := by
  have hp' : Odd p := Nat.odd_iff.mpr hp
  have hr' : Odd r := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hp']
  rcases (show p % 4 = 1 ∨ p % 4 = 3 by omega) with h4 | h4
  · rw [ZMod.χ₄_nat_one_mod_four h4, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h4 hr']
  · rw [ZMod.χ₄_nat_three_mod_four h4, jacobiSym.quadratic_reciprocity_three_mod_four hr h4]
    ring

/- English proof (translation)
Break down `Int.units_eq_one_or s with rfl | rfl` into its components or cases. Conclude with `⟨1, Nat.coprime_one_left _, by simp [jacobiSym.one_left]⟩`. Establish `h1 : 1 ≤ p` using `hp.one_lt.le`. Use `⟨p - 1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]`.

Introduce `h`. Use `Nat.le_of_dvd (by have := hp.two_le; omega) h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hcast : ((p - 1 : ℕ) : ℤ) = -1 + (p : ℤ) * 1` using `by push_cast [h1]; ring`. Rewrite using `[hcast, jacobiSym.mod_left, Int.add_mul_emod_self_left, ← jacobiSym.mod_left (-1) p, jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)), ZMod.χ₄_nat_three_mod_four hp4]`.

Simplify using the standard rewrite rules.
-/
theorem exists_sign {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (s : ℤˣ) :
    ∃ b : ℕ, Nat.Coprime b p ∧ jacobiSym (b : ℤ) p = (s : ℤ) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact ⟨1, Nat.coprime_one_left _, by simp [jacobiSym.one_left]⟩
  · have h1 : 1 ≤ p := hp.one_lt.le
    refine ⟨p - 1, ?_, ?_⟩
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have := Nat.le_of_dvd (by have := hp.two_le; omega) h
      omega
    · have hcast : ((p - 1 : ℕ) : ℤ) = -1 + (p : ℤ) * 1 := by push_cast [h1]; ring
      rw [hcast, jacobiSym.mod_left, Int.add_mul_emod_self_left, ← jacobiSym.mod_left (-1) p,
        jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)), ZMod.χ₄_nat_three_mod_four hp4]
      simp

/- English proof (translation)
Establish `hm0 : m ≠ 0` using `by rintro rfl; exact hm (dvd_zero l)`. Establish `hf : (l ^ k * m).factorization l = k`. Rewrite using `[Nat.factorization_mul (pow_ne_zero _ hl.ne_zero) hm0, Finsupp.add_apply, hl.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm, add_zero]`. Rewrite using `[hf, Nat.mul_div_cancel_left _ (pow_pos hl.pos _)]`.
-/
theorem ordCompl_eq {l m : ℕ} (hl : l.Prime) (k : ℕ) (hm : ¬ l ∣ m) : ordCompl[l] (l ^ k * m) = m := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero l)
  have hf : (l ^ k * m).factorization l = k := by
    rw [Nat.factorization_mul (pow_ne_zero _ hl.ne_zero) hm0, Finsupp.add_apply,
      hl.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  rw [hf, Nat.mul_div_cancel_left _ (pow_pos hl.pos _)]

/- English proof (translation)
Simplify using `only [hcl, QuotientGroup.mk_pow]`.
-/
theorem hcl_pow {e : ℕ} (v : (ZMod (2 ^ (e + 2)))ˣ) (k : ℕ) : hcl e (v ^ k) = hcl e v ^ k := by
  simp only [hcl, QuotientGroup.mk_pow]

variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
include hH

/- English proof (translation)
Apply `Nat.Coprime.pow_left` to reduce the goal to its premises. Rewrite using `[Nat.coprime_primes Nat.prime_two hH.1]`. Use `hH.2.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem cop_2q : Nat.Coprime (2 ^ (e + 2)) q := by
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_primes Nat.prime_two hH.1]
  have := hH.2.2.1
  omega
/- English proof (translation)
Apply `Nat.Coprime.pow_left` to reduce the goal to its premises. Rewrite using `[Nat.coprime_primes Nat.prime_two hH.2.1]`. Use `hH.2.2.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem cop_2d : Nat.Coprime (2 ^ (e + 2)) d := by
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_primes Nat.prime_two hH.2.1]
  have := hH.2.2.2.1
  omega
/- English proof (translation)
Rewrite using `[Nat.coprime_primes hH.1 hH.2.1]`. Use `hH.2.2.1` as an intermediate fact. Use `hH.2.2.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem cop_qd : Nat.Coprime q d := by
  rw [Nat.coprime_primes hH.1 hH.2.1]
  have := hH.2.2.1
  have := hH.2.2.2.1
  omega
/- English proof (translation)
Use `hH.2.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem q4 : q % 4 = 3 := by
  have := hH.2.2.1
  omega
/- English proof (translation)
Use `hH.2.2.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem d4 : d % 4 = 3 := by
  have := hH.2.2.2.1
  omega

/- English proof (translation)
Establish `h` using `hH.2.2.2.2`. Establish `h8` using `hH.2.2.1`. Establish `hq : Odd q` using `Nat.odd_iff.mpr (by omega)`. Rewrite `h` using `[jacobiSym.neg _ hq, ZMod.χ₄_nat_three_mod_four (by omega)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem jac_dq : jacobiSym (d : ℤ) q = -1 := by
  have h := hH.2.2.2.2
  have h8 := hH.2.2.1
  have hq : Odd q := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hq, ZMod.χ₄_nat_three_mod_four (by omega)] at h
  linarith

/- English proof (translation)
Rewrite using `[jacobiSym.quadratic_reciprocity_three_mod_four (q4 hH) (d4 hH), jac_dq hH]`. Evaluate the numerical expressions.
-/
theorem jac_qd : jacobiSym (q : ℤ) d = 1 := by
  rw [jacobiSym.quadratic_reciprocity_three_mod_four (q4 hH) (d4 hH), jac_dq hH]
  norm_num

/- English proof (translation)
Establish `h8` using `hH.2.2.1`. Establish `hq : Odd q` using `Nat.odd_iff.mpr (by omega)`. Rewrite using `[show ((2 : ℕ) : ℤ) = 2 by norm_num, jacobiSym.at_two hq, ZMod.χ₈_nat_eq_if_mod_eight]`. Establish `h2 : q % 2 ≠ 0` using `by omega`. Simplify using `[h2, h8]`.
-/
theorem jac_2q : jacobiSym ((2 : ℕ) : ℤ) q = -1 := by
  have h8 := hH.2.2.1
  have hq : Odd q := Nat.odd_iff.mpr (by omega)
  rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, jacobiSym.at_two hq, ZMod.χ₈_nat_eq_if_mod_eight]
  have h2 : q % 2 ≠ 0 := by omega
  simp [h2, h8]

/- English proof (translation)
Establish `h16` using `hH.2.2.2.1`. Establish `hd : Odd d` using `Nat.odd_iff.mpr (by omega)`. Rewrite using `[show ((2 : ℕ) : ℤ) = 2 by norm_num, jacobiSym.at_two hd, ZMod.χ₈_nat_eq_if_mod_eight]`. Establish `h2 : d % 2 ≠ 0` using `by omega`. Establish `h8 : d % 8 = 7` using `by omega`.

Simplify using `[h2, h8]`.
-/
theorem jac_2d : jacobiSym ((2 : ℕ) : ℤ) d = 1 := by
  have h16 := hH.2.2.2.1
  have hd : Odd d := Nat.odd_iff.mpr (by omega)
  rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, jacobiSym.at_two hd, ZMod.χ₈_nat_eq_if_mod_eight]
  have h2 : d % 2 ≠ 0 := by omega
  have h8 : d % 8 = 7 := by omega
  simp [h2, h8]

/- English proof (translation)
Rewrite using `[mul_assoc]`. Use `ordCompl_eq Nat.prime_two (e + 2) ?_` and prove the remaining obligations. Rewrite using `[Nat.Prime.dvd_mul Nat.prime_two]`. Use `hH.2.2.1` as an intermediate fact. Use `hH.2.2.2.1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem ordCompl_two : ordCompl[2] (2 ^ (e + 2) * q * d) = q * d := by
  rw [mul_assoc]
  refine ordCompl_eq Nat.prime_two (e + 2) ?_
  rw [Nat.Prime.dvd_mul Nat.prime_two]
  have := hH.2.2.1
  have := hH.2.2.2.1
  omega

/- English proof (translation)
Establish `hq` using `hH.1`. Rewrite using `[show 2 ^ (e + 2) * q * d = q ^ 1 * (2 ^ (e + 2) * d) by ring]`. Use `ordCompl_eq hq 1 ?_` and prove the remaining obligations. Rewrite using `[hq.dvd_mul]`. Use `hH.2.2.1` as an intermediate fact.

Use `hH.2.2.2.1` as an intermediate fact. Introduce and unpack `(h | h)`. Establish `h2` using `Nat.le_of_dvd two_pos (hq.dvd_of_dvd_pow h)`. Use linear arithmetic over natural numbers and integers. Establish `h3` using `(Nat.prime_dvd_prime_iff_eq hq hH.2.1).mp h`.

Use linear arithmetic over natural numbers and integers.
-/
theorem ordCompl_q : ordCompl[q] (2 ^ (e + 2) * q * d) = 2 ^ (e + 2) * d := by
  have hq := hH.1
  rw [show 2 ^ (e + 2) * q * d = q ^ 1 * (2 ^ (e + 2) * d) by ring]
  refine ordCompl_eq hq 1 ?_
  rw [hq.dvd_mul]
  have := hH.2.2.1
  have := hH.2.2.2.1
  rintro (h | h)
  · have h2 := Nat.le_of_dvd two_pos (hq.dvd_of_dvd_pow h)
    omega
  · have h3 := (Nat.prime_dvd_prime_iff_eq hq hH.2.1).mp h
    omega

/- English proof (translation)
Establish `hd` using `hH.2.1`. Rewrite using `[show 2 ^ (e + 2) * q * d = d ^ 1 * (2 ^ (e + 2) * q) by ring]`. Use `ordCompl_eq hd 1 ?_` and prove the remaining obligations. Rewrite using `[hd.dvd_mul]`. Use `hH.2.2.1` as an intermediate fact.

Use `hH.2.2.2.1` as an intermediate fact. Introduce and unpack `(h | h)`. Establish `h2` using `Nat.le_of_dvd two_pos (hd.dvd_of_dvd_pow h)`. Use linear arithmetic over natural numbers and integers. Establish `h3` using `(Nat.prime_dvd_prime_iff_eq hd hH.1).mp h`.

Use linear arithmetic over natural numbers and integers.
-/
theorem ordCompl_d : ordCompl[d] (2 ^ (e + 2) * q * d) = 2 ^ (e + 2) * q := by
  have hd := hH.2.1
  rw [show 2 ^ (e + 2) * q * d = d ^ 1 * (2 ^ (e + 2) * q) by ring]
  refine ordCompl_eq hd 1 ?_
  rw [hd.dvd_mul]
  have := hH.2.2.1
  have := hH.2.2.2.1
  rintro (h | h)
  · have h2 := Nat.le_of_dvd two_pos (hd.dvd_of_dvd_pow h)
    omega
  · have h3 := (Nat.prime_dvd_prime_iff_eq hd hH.1).mp h
    omega

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Break down `hl.dvd_mul.mp h with h | h` into its components or cases. Break down `hl.dvd_mul.mp h with h | h` into its components or cases. Conclude with `Or.inl ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h))`.

Conclude with `Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hl hH.1).mp h))`. Conclude with `Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hl hH.2.1).mp h))`. Introduce and unpack `(rfl | rfl | rfl)`. Conclude with `Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _) _`. Conclude with `Dvd.dvd.mul_right (dvd_mul_left _ _) _`.

Conclude with `dvd_mul_left _ _`.
-/
theorem dvd_N_iff {l : ℕ} (hl : l.Prime) : l ∣ 2 ^ (e + 2) * q * d ↔ l = 2 ∨ l = q ∨ l = d := by
  constructor
  · intro h
    rcases hl.dvd_mul.mp h with h | h
    · rcases hl.dvd_mul.mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hl hH.1).mp h))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hl hH.2.1).mp h))
  · rintro (rfl | rfl | rfl)
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _) _
    · exact Dvd.dvd.mul_right (dvd_mul_left _ _) _
    · exact dvd_mul_left _ _

/- English proof (translation)
Establish `h2q` using `cop_2q e hH`. Establish `h2qd : Nat.Coprime (2 ^ (e + 2) * q) d` using `Nat.Coprime.mul (cop_2d e hH) (cop_qd hH)`. Take `⟨n, hn1, hn2⟩` from `Nat.chineseRemainder h2q x y`. Take `⟨m, hm12, hm3⟩` from `Nat.chineseRemainder h2qd n z`. Establish `hm1 : m ≡ x [MOD 2 ^ (e + 2)]` using `(hm12.of_dvd (dvd_mul_right _ _)).trans hn1`.

Establish `hm2 : m ≡ y [MOD q]` using `(hm12.of_dvd (dvd_mul_left _ _)).trans hn2`. Establish `c1 : Nat.Coprime m (2 ^ (e + 2))`. Unfold `Nat.Coprime`. Rewrite using `[hm1.gcd_eq]`. Conclude with `hx`.

Establish `c2 : Nat.Coprime m q`. Unfold `Nat.Coprime`. Rewrite using `[hm2.gcd_eq]`. Conclude with `hy`. Establish `c3 : Nat.Coprime m d`.

Unfold `Nat.Coprime`. Rewrite using `[hm3.gcd_eq]`. Conclude with `hz`. Establish `cN : Nat.Coprime m (2 ^ (e + 2) * q * d)` using `(c1.mul_right c2).mul_right c3`. Apply the tactic sequence `refine ⟨ZMod.unitOfCoprime m cN, ?_, ?_, ?_⟩ <;> rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]`.

Conclude with `((Nat.mod_modEq m _).of_dvd (two_dvd e q d)).trans hm1`. Conclude with `((Nat.mod_modEq m _).of_dvd (q_dvd e q d)).trans hm2`. Conclude with `((Nat.mod_modEq m _).of_dvd (d_dvd e q d)).trans hm3`.
-/
theorem exists_unit (x y z : ℕ) (hx : Nat.Coprime x (2 ^ (e + 2))) (hy : Nat.Coprime y q) (hz : Nat.Coprime z d) :
    ∃ u : (ZMod (2 ^ (e + 2) * q * d))ˣ, (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ x [MOD 2 ^ (e + 2)] ∧
      (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ y [MOD q] ∧ (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ z [MOD d] := by
  have h2q := cop_2q e hH
  have h2qd : Nat.Coprime (2 ^ (e + 2) * q) d := Nat.Coprime.mul (cop_2d e hH) (cop_qd hH)
  obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder h2q x y
  obtain ⟨m, hm12, hm3⟩ := Nat.chineseRemainder h2qd n z
  have hm1 : m ≡ x [MOD 2 ^ (e + 2)] := (hm12.of_dvd (dvd_mul_right _ _)).trans hn1
  have hm2 : m ≡ y [MOD q] := (hm12.of_dvd (dvd_mul_left _ _)).trans hn2
  have c1 : Nat.Coprime m (2 ^ (e + 2)) := by
    unfold Nat.Coprime
    rw [hm1.gcd_eq]
    exact hx
  have c2 : Nat.Coprime m q := by
    unfold Nat.Coprime
    rw [hm2.gcd_eq]
    exact hy
  have c3 : Nat.Coprime m d := by
    unfold Nat.Coprime
    rw [hm3.gcd_eq]
    exact hz
  have cN : Nat.Coprime m (2 ^ (e + 2) * q * d) := (c1.mul_right c2).mul_right c3
  refine ⟨ZMod.unitOfCoprime m cN, ?_, ?_, ?_⟩ <;> rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  · exact ((Nat.mod_modEq m _).of_dvd (two_dvd e q d)).trans hm1
  · exact ((Nat.mod_modEq m _).of_dvd (q_dvd e q d)).trans hm2
  · exact ((Nat.mod_modEq m _).of_dvd (d_dvd e q d)).trans hm3

/- English proof (translation)
Use `haveI := neZeroN e hH`. Establish `h : (art0 e hH u).1.1 = sgnN hH.1 (q_dvd e q d) u` using `rfl`. Rewrite using `[h, sgnN_val]`. Conclude with `jac_congr hu`.
-/
theorem artinMap_first_eq_jacobiSym_of_modEq (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) {y : ℕ} (hu : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ y [MOD q]) :
    (((art0 e hH u).1.1 : ℤˣ) : ℤ) = jacobiSym (y : ℤ) q := by
  haveI := neZeroN e hH
  have h : (art0 e hH u).1.1 = sgnN hH.1 (q_dvd e q d) u := rfl
  rw [h, sgnN_val]
  exact jac_congr hu

/- English proof (translation)
Use `haveI := neZeroN e hH`. Establish `h : (art0 e hH u).1.2 = sgnN hH.2.1 (d_dvd e q d) u` using `rfl`. Rewrite using `[h, sgnN_val]`. Conclude with `jac_congr hu`.
-/
theorem artinMap_second_eq_jacobiSym_of_modEq (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) {y : ℕ} (hu : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ y [MOD d]) :
    (((art0 e hH u).1.2 : ℤˣ) : ℤ) = jacobiSym (y : ℤ) d := by
  haveI := neZeroN e hH
  have h : (art0 e hH u).1.2 = sgnN hH.2.1 (d_dvd e q d) u := rfl
  rw [h, sgnN_val]
  exact jac_congr hu

/- English proof (translation)
Use `haveI := neZeroN e hH`. Establish `h1 : ZMod.unitsMap (two_dvd e q d) u = v`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hv]`. Express the relevant statement in the definitionally equal form `ZMod.cast (u : ZMod (2 ^ (e + 2) * q * d)) = _`.

Rewrite using `[← ZMod.natCast_zmod_val (u : ZMod (2 ^ (e + 2) * q * d)), ZMod.cast_natCast (two_dvd e q d)]`. Conclude with `(ZMod.natCast_eq_natCast_iff _ _ _).mpr hu`. Establish `h2 : (art0 e hH u).2 = QuotientGroup.mk (ZMod.unitsMap (two_dvd e q d) u)` using `rfl`. Rewrite using `[h2, h1]`. Both sides reduce to the same expression.
-/
theorem artinMap_dyadic_eq_of_modEq (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) {y : ℕ}
    (hu : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ y [MOD 2 ^ (e + 2)]) (v : (ZMod (2 ^ (e + 2)))ˣ)
    (hv : (v : ZMod (2 ^ (e + 2))) = (y : ZMod (2 ^ (e + 2)))) : (art0 e hH u).2 = hcl e v := by
  haveI := neZeroN e hH
  have h1 : ZMod.unitsMap (two_dvd e q d) u = v := by
    apply Units.ext
    rw [hv]
    change ZMod.cast (u : ZMod (2 ^ (e + 2) * q * d)) = _
    rw [← ZMod.natCast_zmod_val (u : ZMod (2 ^ (e + 2) * q * d)), ZMod.cast_natCast (two_dvd e q d)]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu
  have h2 : (art0 e hH u).2 = QuotientGroup.mk (ZMod.unitsMap (two_dvd e q d) u) := rfl
  rw [h2, h1]
  rfl

/- English proof (translation)
Establish `hx' : Nat.Coprime x (2 ^ (e + 2))`. Rewrite using `[← ZMod.isUnit_iff_coprime, ← hv]`. Conclude with `v.isUnit`. Establish `hy' : Nat.Coprime y q` using `by haveI : NeZero q := ⟨hH.1.ne_zero⟩`. Establish `h0 : jacobiSym (y : ℤ) q ≠ 0`.

Rewrite using `[← hy]`. Conclude with `Units.ne_zero _`. Establish `h1` using `mt jacobiSym.eq_zero_iff_not_coprime.mpr h0`. Use `push_neg at h1`. Rewrite `h1` using `[Int.gcd_natCast_natCast]`. Then use the resulting hypothesis.

Establish `hz' : Nat.Coprime z d` using `by haveI : NeZero d := ⟨hH.2.1.ne_zero⟩`. Establish `h0 : jacobiSym (z : ℤ) d ≠ 0`. Rewrite using `[← hz]`. Conclude with `Units.ne_zero _`. Establish `h1` using `mt jacobiSym.eq_zero_iff_not_coprime.mpr h0`.

Use `push_neg at h1`. Rewrite `h1` using `[Int.gcd_natCast_natCast]`. Then use the resulting hypothesis. Take `⟨u, h1, h2, h3⟩` from `exists_unit e hH x y z hx' hy' hz'`. Use `⟨u, h1, h2, h3, Prod.ext (Prod.ext (Units.ext ?_) (Units.ext ?_)) ?_⟩` and prove the remaining obligations. Rewrite using `[artinMap_first_eq_jacobiSym_of_modEq e hH u h2, hy]`.

Rewrite using `[artinMap_second_eq_jacobiSym_of_modEq e hH u h3, hz]`. Rewrite using `[artinMap_dyadic_eq_of_modEq e hH u h1 v hv, hx]`.
-/
theorem exists_art (g : FrobeniusOrbits.GG e) (x y z : ℕ) (v : (ZMod (2 ^ (e + 2)))ˣ)
    (hv : (v : ZMod (2 ^ (e + 2))) = (x : ZMod (2 ^ (e + 2)))) (hx : g.2 = hcl e v)
    (hy : ((g.1.1 : ℤˣ) : ℤ) = jacobiSym (y : ℤ) q) (hz : ((g.1.2 : ℤˣ) : ℤ) = jacobiSym (z : ℤ) d) :
    ∃ u : (ZMod (2 ^ (e + 2) * q * d))ˣ, (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ x [MOD 2 ^ (e + 2)] ∧
      (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ y [MOD q] ∧ (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ z [MOD d] ∧
      g = art0 e hH u := by
  have hx' : Nat.Coprime x (2 ^ (e + 2)) := by
    rw [← ZMod.isUnit_iff_coprime, ← hv]
    exact v.isUnit
  have hy' : Nat.Coprime y q := by
    haveI : NeZero q := ⟨hH.1.ne_zero⟩
    have h0 : jacobiSym (y : ℤ) q ≠ 0 := by
      rw [← hy]
      exact Units.ne_zero _
    have h1 := mt jacobiSym.eq_zero_iff_not_coprime.mpr h0
    push_neg at h1
    rwa [Int.gcd_natCast_natCast] at h1
  have hz' : Nat.Coprime z d := by
    haveI : NeZero d := ⟨hH.2.1.ne_zero⟩
    have h0 : jacobiSym (z : ℤ) d ≠ 0 := by
      rw [← hz]
      exact Units.ne_zero _
    have h1 := mt jacobiSym.eq_zero_iff_not_coprime.mpr h0
    push_neg at h1
    rwa [Int.gcd_natCast_natCast] at h1
  obtain ⟨u, h1, h2, h3⟩ := exists_unit e hH x y z hx' hy' hz'
  refine ⟨u, h1, h2, h3, Prod.ext (Prod.ext (Units.ext ?_) (Units.ext ?_)) ?_⟩
  · rw [artinMap_first_eq_jacobiSym_of_modEq e hH u h2, hy]
  · rw [artinMap_second_eq_jacobiSym_of_modEq e hH u h3, hz]
  · rw [artinMap_dyadic_eq_of_modEq e hH u h1 v hv, hx]

omit hH in
/- English proof (translation)
Use `haveI : NeZero (2 ^ (e + 2)) := ⟨by positivity⟩`. Take `⟨v, rfl⟩` from `QuotientGroup.mk_surjective t`. Conclude with `⟨(v : ZMod (2 ^ (e + 2))).val, v, (ZMod.natCast_zmod_val _).symm, rfl⟩`.
-/
theorem exists_rep (t : HGrp e) : ∃ (x : ℕ) (v : (ZMod (2 ^ (e + 2)))ˣ),
    (v : ZMod (2 ^ (e + 2))) = (x : ZMod (2 ^ (e + 2))) ∧ t = hcl e v := by
  haveI : NeZero (2 ^ (e + 2)) := ⟨by positivity⟩
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective t
  exact ⟨(v : ZMod (2 ^ (e + 2))).val, v, (ZMod.natCast_zmod_val _).symm, rfl⟩

/- English proof (translation)
Introduce `g`. Take `⟨x, v, hv, hx⟩` from `exists_rep e g.2`. Take `⟨y, -, hy⟩` from `exists_sign hH.1 (q4 hH) g.1.1`. Take `⟨z, -, hz⟩` from `exists_sign hH.2.1 (d4 hH) g.1.2`. Take `⟨u, -, -, -, hu⟩` from `exists_art e hH g x y z v hv hx hy.symm hz.symm`.

Conclude with `⟨u, hu.symm⟩`.
-/
theorem art0_surjective : Function.Surjective (art0 e hH) := by
  intro g
  obtain ⟨x, v, hv, hx⟩ := exists_rep e g.2
  obtain ⟨y, -, hy⟩ := exists_sign hH.1 (q4 hH) g.1.1
  obtain ⟨z, -, hz⟩ := exists_sign hH.2.1 (d4 hH) g.1.2
  obtain ⟨u, -, -, -, hu⟩ := exists_art e hH g x y z v hv hx hy.symm hz.symm
  exact ⟨u, hu.symm⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg`. Take `⟨x, v, hv, hx⟩` from `exists_rep e g.2`. Establish `h1 : ((g.1.1 : ℤˣ) : ℤ) = jacobiSym ((1 : ℕ) : ℤ) q`. Rewrite using `[hg]`.

Simplify using `[jacobiSym.one_left]`. Establish `h2 : ((g.1.2 : ℤˣ) : ℤ) = jacobiSym ((1 : ℕ) : ℤ) d`. Rewrite using `[hg]`. Simplify using `[jacobiSym.one_left]`. Take `⟨u, -, hq, hd, hu⟩` from `exists_art e hH g x 1 1 v hv hx h1 h2`.

Conclude with `⟨u, (Nat.modEq_and_modEq_iff_modEq_mul (cop_qd hH)).mp ⟨hq, hd⟩, hu⟩`. Introduce and unpack `⟨u, hu, rfl⟩`. Establish `hq : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD q]` using `hu.of_dvd (dvd_mul_right _ _)`. Establish `hd : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD d]` using `hu.of_dvd (dvd_mul_left _ _)`. Use `Prod.ext (Units.ext ?_) (Units.ext ?_)` and prove the remaining obligations.

Rewrite using `[artinMap_first_eq_jacobiSym_of_modEq e hH u hq]`. Simplify using `[jacobiSym.one_left]`. Rewrite using `[artinMap_second_eq_jacobiSym_of_modEq e hH u hd]`. Simplify using `[jacobiSym.one_left]`.
-/
theorem inertia_two (g : FrobeniusOrbits.GG e) : g.1 = 1 ↔ ∃ u : (ZMod (2 ^ (e + 2) * q * d))ˣ,
    (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD q * d] ∧ g = art0 e hH u := by
  constructor
  · intro hg
    obtain ⟨x, v, hv, hx⟩ := exists_rep e g.2
    have h1 : ((g.1.1 : ℤˣ) : ℤ) = jacobiSym ((1 : ℕ) : ℤ) q := by
      rw [hg]
      simp [jacobiSym.one_left]
    have h2 : ((g.1.2 : ℤˣ) : ℤ) = jacobiSym ((1 : ℕ) : ℤ) d := by
      rw [hg]
      simp [jacobiSym.one_left]
    obtain ⟨u, -, hq, hd, hu⟩ := exists_art e hH g x 1 1 v hv hx h1 h2
    exact ⟨u, (Nat.modEq_and_modEq_iff_modEq_mul (cop_qd hH)).mp ⟨hq, hd⟩, hu⟩
  · rintro ⟨u, hu, rfl⟩
    have hq : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD q] := hu.of_dvd (dvd_mul_right _ _)
    have hd : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD d] := hu.of_dvd (dvd_mul_left _ _)
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · rw [artinMap_first_eq_jacobiSym_of_modEq e hH u hq]
      simp [jacobiSym.one_left]
    · rw [artinMap_second_eq_jacobiSym_of_modEq e hH u hd]
      simp [jacobiSym.one_left]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `hg2 : g.2 = hcl e 1`. Apply the tactic sequence `rcases hg with rfl | rfl <;> rfl`. Establish `hg12 : ((g.1.2 : ℤˣ) : ℤ) = jacobiSym ((1 : ℕ) : ℤ) d`.

Apply the tactic sequence `rcases hg with rfl | rfl <;> simp [sg, jacobiSym.one_left]`. Take `⟨y, -, hy⟩` from `exists_sign hH.1 (q4 hH) g.1.1`. Take `⟨u, h1, -, h3, hu⟩` from `exists_art e hH g 1 y 1 1 (by simp) hg2 hy.symm hg12`. Conclude with `⟨u, (Nat.modEq_and_modEq_iff_modEq_mul (cop_2d e hH)).mp ⟨h1, h3⟩, hu⟩`. Introduce and unpack `⟨u, hu, rfl⟩`.

Establish `h2 : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD 2 ^ (e + 2)]` using `hu.of_dvd (dvd_mul_right _ _)`. Establish `h3 : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD d]` using `hu.of_dvd (dvd_mul_left _ _)`. Establish `e2` using `artinMap_dyadic_eq_of_modEq e hH u h2 1 (by simp)`. Establish `e3' : (art0 e hH u).1.2 = 1` using `Units.ext (by rw [artinMap_second_eq_jacobiSym_of_modEq e hH u h3]; simp [jacobiSym.one_left])`. Establish `e2' : (art0 e hH u).2 = 1` using `by rw [e2]; rfl`.

Break down `Int.units_eq_one_or (art0 e hH u).1.1 with h | h` into its components or cases. Conclude with `Or.inl (Prod.ext (Prod.ext h e3') e2')`. Conclude with `Or.inr (Prod.ext (Prod.ext h e3') e2')`.
-/
theorem inertia_q (g : FrobeniusOrbits.GG e) : (g = 1 ∨ g = sg e) ↔ ∃ u : (ZMod (2 ^ (e + 2) * q * d))ˣ,
    (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD 2 ^ (e + 2) * d] ∧ g = art0 e hH u := by
  constructor
  · intro hg
    have hg2 : g.2 = hcl e 1 := by
      rcases hg with rfl | rfl <;> rfl
    have hg12 : ((g.1.2 : ℤˣ) : ℤ) = jacobiSym ((1 : ℕ) : ℤ) d := by
      rcases hg with rfl | rfl <;> simp [sg, jacobiSym.one_left]
    obtain ⟨y, -, hy⟩ := exists_sign hH.1 (q4 hH) g.1.1
    obtain ⟨u, h1, -, h3, hu⟩ := exists_art e hH g 1 y 1 1 (by simp) hg2 hy.symm hg12
    exact ⟨u, (Nat.modEq_and_modEq_iff_modEq_mul (cop_2d e hH)).mp ⟨h1, h3⟩, hu⟩
  · rintro ⟨u, hu, rfl⟩
    have h2 : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD 2 ^ (e + 2)] := hu.of_dvd (dvd_mul_right _ _)
    have h3 : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD d] := hu.of_dvd (dvd_mul_left _ _)
    have e2 := artinMap_dyadic_eq_of_modEq e hH u h2 1 (by simp)
    have e3' : (art0 e hH u).1.2 = 1 := Units.ext (by rw [artinMap_second_eq_jacobiSym_of_modEq e hH u h3]; simp [jacobiSym.one_left])
    have e2' : (art0 e hH u).2 = 1 := by rw [e2]; rfl
    rcases Int.units_eq_one_or (art0 e hH u).1.1 with h | h
    · exact Or.inl (Prod.ext (Prod.ext h e3') e2')
    · exact Or.inr (Prod.ext (Prod.ext h e3') e2')

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `hg2 : g.2 = hcl e 1`. Apply the tactic sequence `rcases hg with rfl | rfl <;> rfl`. Establish `hg11 : ((g.1.1 : ℤˣ) : ℤ) = jacobiSym ((1 : ℕ) : ℤ) q`.

Apply the tactic sequence `rcases hg with rfl | rfl <;> simp [jacobiSym.one_left]`. Take `⟨z, -, hz⟩` from `exists_sign hH.2.1 (d4 hH) g.1.2`. Take `⟨u, h1, h2, -, hu⟩` from `exists_art e hH g 1 1 z 1 (by simp) hg2 hg11 hz.symm`. Conclude with `⟨u, (Nat.modEq_and_modEq_iff_modEq_mul (cop_2q e hH)).mp ⟨h1, h2⟩, hu⟩`. Introduce and unpack `⟨u, hu, rfl⟩`.

Establish `h1 : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD 2 ^ (e + 2)]` using `hu.of_dvd (dvd_mul_right _ _)`. Establish `h2 : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD q]` using `hu.of_dvd (dvd_mul_left _ _)`. Establish `e1` using `artinMap_dyadic_eq_of_modEq e hH u h1 1 (by simp)`. Establish `e2' : (art0 e hH u).1.1 = 1` using `Units.ext (by rw [artinMap_first_eq_jacobiSym_of_modEq e hH u h2]; simp [jacobiSym.one_left])`. Establish `e1' : (art0 e hH u).2 = 1` using `by rw [e1]; rfl`.

Break down `Int.units_eq_one_or (art0 e hH u).1.2 with h | h` into its components or cases. Conclude with `Or.inl (Prod.ext (Prod.ext e2' h) e1')`. Conclude with `Or.inr (Prod.ext (Prod.ext e2' h) e1')`.
-/
theorem inertia_d (g : FrobeniusOrbits.GG e) : (g = 1 ∨ g = ((1, -1), 1)) ↔ ∃ u : (ZMod (2 ^ (e + 2) * q * d))ˣ,
    (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD 2 ^ (e + 2) * q] ∧ g = art0 e hH u := by
  constructor
  · intro hg
    have hg2 : g.2 = hcl e 1 := by
      rcases hg with rfl | rfl <;> rfl
    have hg11 : ((g.1.1 : ℤˣ) : ℤ) = jacobiSym ((1 : ℕ) : ℤ) q := by
      rcases hg with rfl | rfl <;> simp [jacobiSym.one_left]
    obtain ⟨z, -, hz⟩ := exists_sign hH.2.1 (d4 hH) g.1.2
    obtain ⟨u, h1, h2, -, hu⟩ := exists_art e hH g 1 1 z 1 (by simp) hg2 hg11 hz.symm
    exact ⟨u, (Nat.modEq_and_modEq_iff_modEq_mul (cop_2q e hH)).mp ⟨h1, h2⟩, hu⟩
  · rintro ⟨u, hu, rfl⟩
    have h1 : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD 2 ^ (e + 2)] := hu.of_dvd (dvd_mul_right _ _)
    have h2 : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 1 [MOD q] := hu.of_dvd (dvd_mul_left _ _)
    have e1 := artinMap_dyadic_eq_of_modEq e hH u h1 1 (by simp)
    have e2' : (art0 e hH u).1.1 = 1 := Units.ext (by rw [artinMap_first_eq_jacobiSym_of_modEq e hH u h2]; simp [jacobiSym.one_left])
    have e1' : (art0 e hH u).2 = 1 := by rw [e1]; rfl
    rcases Int.units_eq_one_or (art0 e hH u).1.2 with h | h
    · exact Or.inl (Prod.ext (Prod.ext e2' h) e1')
    · exact Or.inr (Prod.ext (Prod.ext e2' h) e1')

/- English proof (translation)
Establish `hJ : ∀ k : ℕ, jacobiSym ((2 ^ k : ℕ) : ℤ) q = (-1) ^ k ∧ jacobiSym ((2 ^ k : ℕ) : ℤ) d = 1`. Introduce `k`. Rewrite using `[Nat.cast_pow, jacobiSym.pow_left, jacobiSym.pow_left, jac_2q hH, jac_2d hH, one_pow]`. Conclude with `⟨rfl, rfl⟩`. Prove the components needed by the constructor for the conclusion.

Introduce `hg`. Take `⟨x, v, hv, hx⟩` from `exists_rep e g.2`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k : ℕ, ((g.1.1 : ℤˣ) : ℤ) = (-1) ^ k := by`. Break down `Int.units_eq_one_or g.1.1 with h | h` into its components or cases. Conclude with `⟨0, by simp [h]⟩`.

Conclude with `⟨1, by simp [h]⟩`. Take `⟨u, -, hq, hd, hu⟩` from `exists_art e hH g x (2 ^ k) (2 ^ k) v hv hx (by rw [hk, (hJ k).1]) (by rw [hg, Units.val_one, (hJ k).2])`. Conclude with `⟨u, k, (Nat.modEq_and_modEq_iff_modEq_mul (cop_qd hH)).mp ⟨hq, hd⟩, hu⟩`. Introduce and unpack `⟨u, k, hu, rfl⟩`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[artinMap_second_eq_jacobiSym_of_modEq e hH u (hu.of_dvd (dvd_mul_left _ _)), (hJ k).2, Units.val_one]`.
-/
theorem decomp_two (g : FrobeniusOrbits.GG e) : g.1.2 = 1 ↔ ∃ (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) (k : ℕ),
    (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ 2 ^ k [MOD q * d] ∧ g = art0 e hH u := by
  have hJ : ∀ k : ℕ, jacobiSym ((2 ^ k : ℕ) : ℤ) q = (-1) ^ k ∧ jacobiSym ((2 ^ k : ℕ) : ℤ) d = 1 := by
    intro k
    rw [Nat.cast_pow, jacobiSym.pow_left, jacobiSym.pow_left, jac_2q hH, jac_2d hH, one_pow]
    exact ⟨rfl, rfl⟩
  constructor
  · intro hg
    obtain ⟨x, v, hv, hx⟩ := exists_rep e g.2
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ((g.1.1 : ℤˣ) : ℤ) = (-1) ^ k := by
      rcases Int.units_eq_one_or g.1.1 with h | h
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
    obtain ⟨u, -, hq, hd, hu⟩ := exists_art e hH g x (2 ^ k) (2 ^ k) v hv hx
      (by rw [hk, (hJ k).1]) (by rw [hg, Units.val_one, (hJ k).2])
    exact ⟨u, k, (Nat.modEq_and_modEq_iff_modEq_mul (cop_qd hH)).mp ⟨hq, hd⟩, hu⟩
  · rintro ⟨u, k, hu, rfl⟩
    apply Units.ext
    rw [artinMap_second_eq_jacobiSym_of_modEq e hH u (hu.of_dvd (dvd_mul_left _ _)), (hJ k).2, Units.val_one]

/- English proof (translation)
Establish `hJ : ∀ k : ℕ, jacobiSym ((q ^ k : ℕ) : ℤ) d = 1`. Introduce `k`. Rewrite using `[Nat.cast_pow, jacobiSym.pow_left, jac_qd hH, one_pow]`. Establish `hV : ∀ k : ℕ, ((uq ^ k : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = ((q ^ k : ℕ) : ZMod _)`. Introduce `k`.

Rewrite using `[Units.val_pow_eq_pow_val, huq, Nat.cast_pow]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hg, k, hk⟩`. Take `⟨y, -, hy⟩` from `exists_sign hH.1 (q4 hH) g.1.1`. Take `⟨u, h1, -, h3, hu⟩` from `exists_art e hH g (q ^ k) y (q ^ k) (uq ^ k) (hV k) (by rw [hk, hcl_pow]) hy.symm (by rw [hg, Units.val_one, hJ k])`.

Conclude with `⟨u, k, (Nat.modEq_and_modEq_iff_modEq_mul (cop_2d e hH)).mp ⟨h1, h3⟩, hu⟩`. Introduce and unpack `⟨u, k, hu, rfl⟩`. Use `⟨Units.ext ?_, k, ?_⟩` and prove the remaining obligations. Rewrite using `[artinMap_second_eq_jacobiSym_of_modEq e hH u (hu.of_dvd (dvd_mul_left _ _)), hJ k, Units.val_one]`. Rewrite using `[artinMap_dyadic_eq_of_modEq e hH u (hu.of_dvd (dvd_mul_right _ _)) (uq ^ k) (hV k), hcl_pow]`.
-/
theorem decomp_q (uq : (ZMod (2 ^ (e + 2)))ˣ) (huq : (uq : ZMod (2 ^ (e + 2))) = (q : ZMod _)) (g : FrobeniusOrbits.GG e) :
    (g.1.2 = 1 ∧ ∃ k : ℕ, g.2 = hcl e uq ^ k) ↔ ∃ (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) (k : ℕ),
    (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ q ^ k [MOD 2 ^ (e + 2) * d] ∧ g = art0 e hH u := by
  have hJ : ∀ k : ℕ, jacobiSym ((q ^ k : ℕ) : ℤ) d = 1 := by
    intro k
    rw [Nat.cast_pow, jacobiSym.pow_left, jac_qd hH, one_pow]
  have hV : ∀ k : ℕ, ((uq ^ k : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = ((q ^ k : ℕ) : ZMod _) := by
    intro k
    rw [Units.val_pow_eq_pow_val, huq, Nat.cast_pow]
  constructor
  · rintro ⟨hg, k, hk⟩
    obtain ⟨y, -, hy⟩ := exists_sign hH.1 (q4 hH) g.1.1
    obtain ⟨u, h1, -, h3, hu⟩ := exists_art e hH g (q ^ k) y (q ^ k) (uq ^ k) (hV k)
      (by rw [hk, hcl_pow]) hy.symm (by rw [hg, Units.val_one, hJ k])
    exact ⟨u, k, (Nat.modEq_and_modEq_iff_modEq_mul (cop_2d e hH)).mp ⟨h1, h3⟩, hu⟩
  · rintro ⟨u, k, hu, rfl⟩
    refine ⟨Units.ext ?_, k, ?_⟩
    · rw [artinMap_second_eq_jacobiSym_of_modEq e hH u (hu.of_dvd (dvd_mul_left _ _)), hJ k, Units.val_one]
    · rw [artinMap_dyadic_eq_of_modEq e hH u (hu.of_dvd (dvd_mul_right _ _)) (uq ^ k) (hV k), hcl_pow]

/- English proof (translation)
Establish `hJ : ∀ k : ℕ, jacobiSym ((d ^ k : ℕ) : ℤ) q = (-1) ^ k`. Introduce `k`. Rewrite using `[Nat.cast_pow, jacobiSym.pow_left, jac_dq hH]`. Establish `hV : ∀ k : ℕ, ((ud ^ k : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = ((d ^ k : ℕ) : ZMod _)`. Introduce `k`.

Rewrite using `[Units.val_pow_eq_pow_val, hud, Nat.cast_pow]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk1, hk2⟩`. Take `⟨z, -, hz⟩` from `exists_sign hH.2.1 (d4 hH) g.1.2`. Take `⟨u, h1, h2, -, hu⟩` from `exists_art e hH g (d ^ k) (d ^ k) z (ud ^ k) (hV k) (by rw [hk2, hcl_pow]) (by rw [hk1, hJ k]; push_cast; rfl) hz.symm`.

Conclude with `⟨u, k, (Nat.modEq_and_modEq_iff_modEq_mul (cop_2q e hH)).mp ⟨h1, h2⟩, hu⟩`. Introduce and unpack `⟨u, k, hu, rfl⟩`. Use `⟨k, Units.ext ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[artinMap_first_eq_jacobiSym_of_modEq e hH u (hu.of_dvd (dvd_mul_left _ _)), hJ k]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[artinMap_dyadic_eq_of_modEq e hH u (hu.of_dvd (dvd_mul_right _ _)) (ud ^ k) (hV k), hcl_pow]`.
-/
theorem decomp_d (ud : (ZMod (2 ^ (e + 2)))ˣ) (hud : (ud : ZMod (2 ^ (e + 2))) = (d : ZMod _)) (g : FrobeniusOrbits.GG e) :
    (∃ k : ℕ, g.1.1 = (-1) ^ k ∧ g.2 = hcl e ud ^ k) ↔ ∃ (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) (k : ℕ),
    (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ d ^ k [MOD 2 ^ (e + 2) * q] ∧ g = art0 e hH u := by
  have hJ : ∀ k : ℕ, jacobiSym ((d ^ k : ℕ) : ℤ) q = (-1) ^ k := by
    intro k
    rw [Nat.cast_pow, jacobiSym.pow_left, jac_dq hH]
  have hV : ∀ k : ℕ, ((ud ^ k : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = ((d ^ k : ℕ) : ZMod _) := by
    intro k
    rw [Units.val_pow_eq_pow_val, hud, Nat.cast_pow]
  constructor
  · rintro ⟨k, hk1, hk2⟩
    obtain ⟨z, -, hz⟩ := exists_sign hH.2.1 (d4 hH) g.1.2
    obtain ⟨u, h1, h2, -, hu⟩ := exists_art e hH g (d ^ k) (d ^ k) z (ud ^ k) (hV k)
      (by rw [hk2, hcl_pow]) (by rw [hk1, hJ k]; push_cast; rfl) hz.symm
    exact ⟨u, k, (Nat.modEq_and_modEq_iff_modEq_mul (cop_2q e hH)).mp ⟨h1, h2⟩, hu⟩
  · rintro ⟨u, k, hu, rfl⟩
    refine ⟨k, Units.ext ?_, ?_⟩
    · rw [artinMap_first_eq_jacobiSym_of_modEq e hH u (hu.of_dvd (dvd_mul_left _ _)), hJ k]
      push_cast
      rfl
    · rw [artinMap_dyadic_eq_of_modEq e hH u (hu.of_dvd (dvd_mul_right _ _)) (ud ^ k) (hV k), hcl_pow]

/- English proof (translation)
Use `haveI := neZeroN e hH`. Establish `hup : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ p [MOD 2 ^ (e + 2) * q * d]` using `(ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [ZMod.natCast_zmod_val, hu])`. Establish `eq1 : (((art0 e hH u).1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p`. Rewrite using `[artinMap_first_eq_jacobiSym_of_modEq e hH u (hup.of_dvd (q_dvd e q d)), jac_recip (q4 hH) hp]`. Establish `eq2 : (((art0 e hH u).1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p`.

Rewrite using `[artinMap_second_eq_jacobiSym_of_modEq e hH u (hup.of_dvd (d_dvd e q d)), jac_recip (d4 hH) hp]`. Establish `hc : Nat.Coprime p (2 ^ (e + 2))`. Establish `: Nat.Coprime p 2`. Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]`. Use linear arithmetic over natural numbers and integers.

Conclude with `this.pow_right (e + 2)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, v, hv, h3⟩`. Conclude with `Prod.ext (Prod.ext (Units.ext (h1.trans eq1.symm)) (Units.ext (h2.trans eq2.symm))) (h3.trans (artinMap_dyadic_eq_of_modEq e hH u (hup.of_dvd (two_dvd e q d)) v hv).symm)`. Introduce and unpack `rfl`.

Conclude with `⟨eq1, eq2, ZMod.unitOfCoprime p hc, ZMod.coe_unitOfCoprime _ _, artinMap_dyadic_eq_of_modEq e hH u (hup.of_dvd (two_dvd e q d)) _ (ZMod.coe_unitOfCoprime _ _)⟩`.
-/
theorem frob_iff {p : ℕ} (hp : p % 2 = 1) (u : (ZMod (2 ^ (e + 2) * q * d))ˣ)
    (hu : (u : ZMod (2 ^ (e + 2) * q * d)) = (p : ZMod (2 ^ (e + 2) * q * d))) (g : FrobeniusOrbits.GG e) :
    (((g.1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧ ((g.1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p ∧
      ∃ v : (ZMod (2 ^ (e + 2)))ˣ, (v : ZMod (2 ^ (e + 2))) = (p : ZMod _) ∧ g.2 = hcl e v) ↔ g = art0 e hH u := by
  haveI := neZeroN e hH
  have hup : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ p [MOD 2 ^ (e + 2) * q * d] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [ZMod.natCast_zmod_val, hu])
  have eq1 : (((art0 e hH u).1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p := by
    rw [artinMap_first_eq_jacobiSym_of_modEq e hH u (hup.of_dvd (q_dvd e q d)), jac_recip (q4 hH) hp]
  have eq2 : (((art0 e hH u).1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p := by
    rw [artinMap_second_eq_jacobiSym_of_modEq e hH u (hup.of_dvd (d_dvd e q d)), jac_recip (d4 hH) hp]
  have hc : Nat.Coprime p (2 ^ (e + 2)) := by
    have : Nat.Coprime p 2 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      omega
    exact this.pow_right (e + 2)
  constructor
  · rintro ⟨h1, h2, v, hv, h3⟩
    exact Prod.ext (Prod.ext (Units.ext (h1.trans eq1.symm)) (Units.ext (h2.trans eq2.symm)))
      (h3.trans (artinMap_dyadic_eq_of_modEq e hH u (hup.of_dvd (two_dvd e q d)) v hv).symm)
  · rintro rfl
    exact ⟨eq1, eq2, ZMod.unitOfCoprime p hc, ZMod.coe_unitOfCoprime _ _,
      artinMap_dyadic_eq_of_modEq e hH u (hup.of_dvd (two_dvd e q d)) _ (ZMod.coe_unitOfCoprime _ _)⟩

end Formalism.HC.D7

end
