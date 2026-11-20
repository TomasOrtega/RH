import Mathlib
import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Classical

/- English proof (translation)
Establish `key : ∀ (R : Ranks) (t : R.A), Odd (addOrderOf t) → R.toFrame.h t = 0 ∧ addOrderOf t ∣ R.toFrame.o`. Introduce `R t ho`. Establish `h1` using `R.toFrame.addOrderOf_h_dvd t`. Establish `h2` using `R.toFrame.addOrderOf_h_dvd_two_pow t`. Establish `hcop : Nat.Coprime (addOrderOf t) (2 ^ R.toFrame.e)` using `Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 ho)`.

Establish `h3 : addOrderOf (R.toFrame.h t) = 1` using `Nat.eq_one_of_dvd_coprimes hcop h1 h2`. Establish `h0 : R.toFrame.h t = 0` using `AddMonoid.addOrderOf_eq_one_iff.1 h3`. Conclude with `⟨h0, addOrderOf_dvd_iff_nsmul_eq_zero.2 (R.toFrame.o_nsmul_of_h_eq_zero h0)⟩`. Use `⟨key, fun D L p hx => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Establish `hd` using `(key D.R (hP D p) (Nat.not_even_iff_odd.1 hne)).2`. Establish `hle : addOrderOf (hP D p) ≤ D.R.toFrame.o` using `Nat.le_of_dvd D.R.toFrame.o_pos hd`. Establish `hle' : (addOrderOf (hP D p) : ℝ) ≤ (D.R.o : ℝ)` using `by exact_mod_cast hle`. Establish `hlt : L.sc.x ^ (L.sc.eps / 100) < L.sc.x ^ (L.sc.eps / 4)` using `Real.rpow_lt_rpow_of_exponent_lt L.sc.one_lt_alt (by linarith [L.sc.eps_pos])`. Combine the linear relations using `[L.o_tie]`.
-/
theorem UpperTheory.even_addOrderOf_hP_of_pow_le :
    (∀ (R : Ranks) (t : R.A), Odd (addOrderOf t) → R.toFrame.h t = 0 ∧ addOrderOf t ∣ R.toFrame.o) ∧
    ∀ (D : D7) (L : SizeData₂ D) (p : ℕ), L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (hP D p) : ℝ) → Even (addOrderOf (hP D p)) := by
  have key : ∀ (R : Ranks) (t : R.A), Odd (addOrderOf t) →
      R.toFrame.h t = 0 ∧ addOrderOf t ∣ R.toFrame.o := by
    intro R t ho
    have h1 := R.toFrame.addOrderOf_h_dvd t
    have h2 := R.toFrame.addOrderOf_h_dvd_two_pow t
    have hcop : Nat.Coprime (addOrderOf t) (2 ^ R.toFrame.e) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 ho)
    have h3 : addOrderOf (R.toFrame.h t) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    have h0 : R.toFrame.h t = 0 := AddMonoid.addOrderOf_eq_one_iff.1 h3
    exact ⟨h0, addOrderOf_dvd_iff_nsmul_eq_zero.2 (R.toFrame.o_nsmul_of_h_eq_zero h0)⟩
  refine ⟨key, fun D L p hx => ?_⟩
  by_contra hne
  have hd := (key D.R (hP D p) (Nat.not_even_iff_odd.1 hne)).2
  have hle : addOrderOf (hP D p) ≤ D.R.toFrame.o := Nat.le_of_dvd D.R.toFrame.o_pos hd
  have hle' : (addOrderOf (hP D p) : ℝ) ≤ (D.R.o : ℝ) := by exact_mod_cast hle
  have hlt : L.sc.x ^ (L.sc.eps / 100) < L.sc.x ^ (L.sc.eps / 4) :=
    Real.rpow_lt_rpow_of_exponent_lt L.sc.one_lt_alt (by linarith [L.sc.eps_pos])
  linarith [L.o_tie]
