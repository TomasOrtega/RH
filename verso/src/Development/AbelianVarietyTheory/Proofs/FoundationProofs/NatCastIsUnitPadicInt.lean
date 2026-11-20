import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

namespace GlobalTheory.PadicInversePower

open Formalism.ConjugateSelfDual

/- English proof (translation)
Rewrite using `[PadicInt.isUnit_iff]`. Use `le_antisymm (PadicInt.norm_le_one _) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `: ‖((n : ℤ) : ℤ_[l])‖ < 1` using `by simpa using hlt`.

Rewrite `this` using `[PadicInt.norm_int_lt_one_iff_dvd]`. Conclude with `h (Int.natCast_dvd_natCast.mp this)`.
-/
theorem natCast_isUnit_padicInt (l : ℕ) [Fact (Nat.Prime l)] (n : ℕ) (h : ¬ l ∣ n) : IsUnit (n : ℤ_[l]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) ?_
  by_contra hlt
  push_neg at hlt
  have : ‖((n : ℤ) : ℤ_[l])‖ < 1 := by simpa using hlt
  rw [PadicInt.norm_int_lt_one_iff_dvd] at this
  exact h (Int.natCast_dvd_natCast.mp this)

/- English proof (translation)
Break down `Nat.eq_zero_or_pos r with rfl | hr` into its components or cases. Establish `h0 : (x : ZMod (l ^ 0)).val = 0` using `by haveI : NeZero (l ^ 0) := ⟨by simp⟩`. Use `ZMod.val_lt (x : ZMod (l ^ 0))` as an intermediate fact. Simplify using `only [pow_zero] at this`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[h0]`. Break down `Nat.eq_zero_or_pos e with rfl | he` into its components or cases. Simplify using `only [pow_zero, inv_one]`. Conclude with `c.O.one_mem`. Simplify using `only [Nat.cast_zero, zero_pow he.ne', inv_zero]`.

Conclude with `c.O.zero_mem`. Use `set n := (x : ZMod (l ^ r)).val with hn`. Establish `hcop : Nat.Coprime n (l ^ r)` using `ZMod.val_coe_unit_coprime x`. Establish `hnd : ¬ l ∣ n`. Introduce `hd`.

Use `Nat.Coprime.coprime_dvd_left hd hcop` as an intermediate fact. Establish `h1 : Nat.Coprime l l` using `Nat.Coprime.coprime_dvd_right (dvd_pow_self l hr.ne') this`. Establish `hl1 : l = 1` using `by simpa using h1`. Conclude with `(Fact.out : Nat.Prime l).one_lt.ne' hl1`. Take `⟨u, hu⟩` from `natCast_isUnit_padicInt l n hnd`.

Establish `key : (((n : ℕ) : Formalism.ConjugateSelfDual.Qbar l) ^ e)⁻¹ = algebraMap ℤ_[l] (Formalism.ConjugateSelfDual.Qbar l) ((u⁻¹ : ℤ_[l]ˣ) ^ e : ℤ_[l]ˣ)`. Rewrite using `[Units.val_pow_eq_pow_val, map_pow, ← inv_pow, ← map_natCast (algebraMap ℤ_[l] (Formalism.ConjugateSelfDual.Qbar l)) n, ← hu]`. Use `congr 1`. Use `symm`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises.

Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Rewrite using `[key]`. Conclude with `c.O.algebraMap_mem _`.
-/
theorem inv_pow_mem (l : ℕ) [Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l) (e r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    ((((x : ZMod (l ^ r)).val : ℕ) : Formalism.ConjugateSelfDual.Qbar l) ^ e)⁻¹ ∈ UpperTheory.V.HV.Coef.O c := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h0 : (x : ZMod (l ^ 0)).val = 0 := by
      haveI : NeZero (l ^ 0) := ⟨by simp⟩
      have := ZMod.val_lt (x : ZMod (l ^ 0))
      simp only [pow_zero] at this
      omega
    rw [h0]
    rcases Nat.eq_zero_or_pos e with rfl | he
    · simp only [pow_zero, inv_one]; exact c.O.one_mem
    · simp only [Nat.cast_zero, zero_pow he.ne', inv_zero]; exact c.O.zero_mem
  · set n := (x : ZMod (l ^ r)).val with hn
    have hcop : Nat.Coprime n (l ^ r) := ZMod.val_coe_unit_coprime x
    have hnd : ¬ l ∣ n := by
      intro hd
      have := Nat.Coprime.coprime_dvd_left hd hcop
      have h1 : Nat.Coprime l l := Nat.Coprime.coprime_dvd_right (dvd_pow_self l hr.ne') this
      have hl1 : l = 1 := by simpa using h1
      exact (Fact.out : Nat.Prime l).one_lt.ne' hl1
    obtain ⟨u, hu⟩ := natCast_isUnit_padicInt l n hnd
    have key : (((n : ℕ) : Formalism.ConjugateSelfDual.Qbar l) ^ e)⁻¹ = algebraMap ℤ_[l] (Formalism.ConjugateSelfDual.Qbar l) ((u⁻¹ : ℤ_[l]ˣ) ^ e : ℤ_[l]ˣ) := by
      rw [Units.val_pow_eq_pow_val, map_pow, ← inv_pow, ← map_natCast (algebraMap ℤ_[l] (Formalism.ConjugateSelfDual.Qbar l)) n, ← hu]
      congr 1
      symm
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    rw [key]
    exact c.O.algebraMap_mem _

end GlobalTheory.PadicInversePower
