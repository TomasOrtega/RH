import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : ((n : ℤ) * q.num : ℚ) = (a * q.den : ℤ)`. Use `push_cast`. Rewrite using `[← Rat.mul_den_eq_num q, ← mul_assoc, h]`. Establish `h2 : (n : ℤ) * q.num = a * q.den` using `by exact_mod_cast h1`. Establish `h3 : (q.den : ℤ) ∣ (n : ℤ) * q.num` using `⟨a, by rw [h2]; ring⟩`.

Establish `h4 : q.den ∣ n * q.num.natAbs`. Use `Int.natAbs_dvd_natAbs.mpr h3` as an intermediate fact. Simplify `this` using `[Int.natAbs_mul]`. Conclude with `(Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.symm q.reduced) h4)`.
-/
theorem den_dvd_of_natCast_mul_eq_int (n : ℕ) (q : ℚ) (a : ℤ) (h : (n : ℚ) * q = a) :
    q.den ∣ n := by
  have h1 : ((n : ℤ) * q.num : ℚ) = (a * q.den : ℤ) := by
    push_cast
    rw [← Rat.mul_den_eq_num q, ← mul_assoc, h]
  have h2 : (n : ℤ) * q.num = a * q.den := by exact_mod_cast h1
  have h3 : (q.den : ℤ) ∣ (n : ℤ) * q.num := ⟨a, by rw [h2]; ring⟩
  have h4 : q.den ∣ n * q.num.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr h3
    simpa [Int.natAbs_mul] using this
  exact (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.symm q.reduced) h4)

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Use `⟨c * q.num, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[← Rat.mul_den_eq_num q]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_int_of_den_dvd (n : ℕ) (q : ℚ) (h : q.den ∣ n) :
    ∃ a : ℤ, (n : ℚ) * q = a := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨c * q.num, ?_⟩
  push_cast
  rw [← Rat.mul_den_eq_num q]
  ring

/- English proof (translation)
Introduce `p D K k _ q ⟨m, hm, a, ha⟩ ⟨b, hb⟩`. Establish `d1` using `den_dvd_of_natCast_mul_eq_int _ q a ha`. Establish `d2` using `den_dvd_of_natCast_mul_eq_int _ q b hb`. Apply `exists_int_of_den_dvd` to reduce the goal to its premises. Establish `e1 : q.den ∣ D * p ^ K * m`.

Establish `: p ^ K * m ∣ D * p ^ K * m` using `⟨D, by ring⟩`. Conclude with `d1.trans this`. Establish `e2 : q.den ∣ D * p ^ K * p ^ k`. Establish `: D * p ^ k ∣ D * p ^ K * p ^ k` using `⟨p ^ K, by ring⟩`. Conclude with `d2.trans this`.

Establish `e3` using `Nat.dvd_gcd e1 e2`. Rewrite `e3` using `[Nat.gcd_mul_left, (Nat.Coprime.pow_right k hm : Nat.Coprime m (p ^ k)), mul_one]`. Conclude with `e3`.
-/
theorem den_comb : ∀ (p D K k : ℕ), p.Prime → ∀ q : ℚ,
    (∃ m : ℕ, m.Coprime p ∧ ∃ a : ℤ, ((p ^ K * m : ℕ) : ℚ) * q = a) →
    (∃ a : ℤ, ((D * p ^ k : ℕ) : ℚ) * q = a) →
    ∃ a : ℤ, ((D * p ^ K : ℕ) : ℚ) * q = a := by
  intro p D K k _ q ⟨m, hm, a, ha⟩ ⟨b, hb⟩
  have d1 := den_dvd_of_natCast_mul_eq_int _ q a ha
  have d2 := den_dvd_of_natCast_mul_eq_int _ q b hb
  apply exists_int_of_den_dvd
  have e1 : q.den ∣ D * p ^ K * m := by
    have : p ^ K * m ∣ D * p ^ K * m := ⟨D, by ring⟩
    exact d1.trans this
  have e2 : q.den ∣ D * p ^ K * p ^ k := by
    have : D * p ^ k ∣ D * p ^ K * p ^ k := ⟨p ^ K, by ring⟩
    exact d2.trans this
  have e3 := Nat.dvd_gcd e1 e2
  rw [Nat.gcd_mul_left, (Nat.Coprime.pow_right k hm : Nat.Coprime m (p ^ k)), mul_one] at e3
  exact e3

end GlobalTheory
