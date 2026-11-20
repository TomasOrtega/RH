import Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower

noncomputable section

open NumberField

namespace Formalism.L2.Host

/- English proof (translation)
Use `haveI := Fact.mk hq`. Use `haveI := Fact.mk hp`. Establish `hpq : p ≠ q`. Introduce and unpack `rfl`. Establish `h0 : (v : ZMod p) = 0`.

Rewrite using `[hv]`. Conclude with `ZMod.natCast_self p`. Conclude with `v.ne_zero h0`. Establish `hq2 : q ≠ 2`. Introduce and unpack `rfl`.

Evaluate the numerical expressions using `at hq4`. Establish `hp0 : ((p : ℤ) : ZMod q) ≠ 0`. Rewrite using `[Int.cast_natCast, ← hv]`. Conclude with `v.ne_zero`. Establish `hq0 : ((q : ℤ) : ZMod p) ≠ 0`.

Rewrite using `[Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]`. Introduce `hd`. Conclude with `hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 hd)`. Establish `hpodd : p % 2 = 1` using `Nat.odd_iff.1 (hp.odd_of_ne_two hp2)`. Establish `key : legendreSym p (-(q : ℤ)) = legendreSym q p`.

Rewrite using `[show (-(q : ℤ)) = -1 * q by ring, legendreSym.mul, legendreSym.at_neg_one hp2, ZMod.χ₄_eq_neg_one_pow hpodd]`. Establish `hp4 : p % 4 = 1 ∨ p % 4 = 3` using `by omega`. Break down `hp4 with h4 | h4` into its components or cases. Establish `hp2' : (p / 2) % 2 = 0` using `by omega`. Rewrite using `[legendreSym.quadratic_reciprocity_one_mod_four h4 hq2, (Nat.even_iff.2 hp2').neg_one_pow, one_mul]`.

Establish `hp2' : (p / 2) % 2 = 1` using `by omega`. Rewrite using `[legendreSym.quadratic_reciprocity_three_mod_four h4 hq4, (Nat.odd_iff.2 hp2').neg_one_pow, neg_one_mul]`. Rewrite using `[← jacobiSym.legendreSym.to_jacobiSym, key]`. Unfold `sqSign`. Use `split_ifs with h`.

Rewrite using `[Units.val_one, eq_comm, legendreSym.eq_one_iff q hp0, Int.cast_natCast, ← hv]`. Conclude with `h`. Rewrite using `[Units.val_neg, Units.val_one, eq_comm, legendreSym.eq_neg_one_iff q, Int.cast_natCast, ← hv]`. Conclude with `h`.
-/
theorem sqSign_eq_jacobi {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hq4 : q % 4 = 3) (hp2 : p ≠ 2)
    (v : (ZMod q)ˣ) (hv : (v : ZMod q) = (p : ZMod q)) :
    ((sqSign v : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p := by
  haveI := Fact.mk hq
  haveI := Fact.mk hp
  have hpq : p ≠ q := by
    rintro rfl
    have h0 : (v : ZMod p) = 0 := by
      rw [hv]
      exact ZMod.natCast_self p
    exact v.ne_zero h0
  have hq2 : q ≠ 2 := by
    rintro rfl
    norm_num at hq4
  have hp0 : ((p : ℤ) : ZMod q) ≠ 0 := by
    rw [Int.cast_natCast, ← hv]
    exact v.ne_zero
  have hq0 : ((q : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 hd)
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  have key : legendreSym p (-(q : ℤ)) = legendreSym q p := by
    rw [show (-(q : ℤ)) = -1 * q by ring, legendreSym.mul, legendreSym.at_neg_one hp2,
      ZMod.χ₄_eq_neg_one_pow hpodd]
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hp4 with h4 | h4
    · have hp2' : (p / 2) % 2 = 0 := by omega
      rw [legendreSym.quadratic_reciprocity_one_mod_four h4 hq2,
        (Nat.even_iff.2 hp2').neg_one_pow, one_mul]
    · have hp2' : (p / 2) % 2 = 1 := by omega
      rw [legendreSym.quadratic_reciprocity_three_mod_four h4 hq4,
        (Nat.odd_iff.2 hp2').neg_one_pow, neg_one_mul]
  rw [← jacobiSym.legendreSym.to_jacobiSym, key]
  unfold sqSign
  split_ifs with h
  · rw [Units.val_one, eq_comm, legendreSym.eq_one_iff q hp0, Int.cast_natCast, ← hv]
    exact h
  · rw [Units.val_neg, Units.val_one, eq_comm, legendreSym.eq_neg_one_iff q, Int.cast_natCast, ← hv]
    exact h

end Formalism.L2.Host
