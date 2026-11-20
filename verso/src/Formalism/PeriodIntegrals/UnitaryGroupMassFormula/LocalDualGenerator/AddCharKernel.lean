import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.FpDualUnram

namespace PI.LocDualGen.Psi

open PI.LocDualGen.W

/- English proof (translation)
Introduce and unpack `l _ t a ⟨n, hn⟩ ht`. Establish `hI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`. Establish `hexp : Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) = 1 ↔ a.den = 1`. Rewrite using `[Complex.exp_eq_one_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm⟩`. Rewrite `hm` using `[mul_comm (m : ℂ)]`. Establish `h1 : (a : ℂ) = (m : ℂ)` using `mul_left_cancel₀ hI hm`. Establish `ha : a = m` using `by exact_mod_cast h1`.

Rewrite using `[ha]`. Conclude with `Rat.den_intCast m`. Introduce `h1`. Use `⟨a.num, ?_⟩` and prove the remaining obligations. Establish `ha : (a : ℂ) = (a.num : ℂ)`.

Establish `h` using `(Rat.den_eq_one_iff a).mp h1`. Conclude with `h.symm` after adjusting the coercions. Rewrite using `[ha]`. Expand and normalize the polynomial expressions, which then agree. Establish `hna : ‖t‖ ≤ 1 ↔ ‖(a : ℚ_[l])‖ ≤ 1`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `e : (a : ℚ_[l]) = t + ((a : ℚ_[l]) - t)` using `by ring`. Rewrite using `[e]`. Use `le_trans (Padic.nonarchimedean _ _) (max_le h ?_)` and prove the remaining obligations.

Rewrite using `[norm_sub_rev]`. Conclude with `ht`. Introduce `h`. Establish `e : t = (t - (a : ℚ_[l])) + (a : ℚ_[l])` using `by ring`. Rewrite using `[e]`.

Conclude with `le_trans (Padic.nonarchimedean _ _) (max_le ht h)`. Establish `hrat : ‖(a : ℚ_[l])‖ ≤ 1 ↔ a.den = 1`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hd`.

Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Rewrite `hn` using `[pow_zero]`. Conclude with `hd hn`. Establish `hlp : l.Prime` using `Fact.out`.

Establish `hnum : ¬ (l : ℤ) ∣ a.num`. Introduce `hdvd`. Establish `h1 : l ∣ a.num.natAbs` using `Int.natCast_dvd.mp hdvd`. Establish `h2 : l ∣ a.den`. Rewrite using `[hn]`.

Conclude with `dvd_pow_self l hn0`. Establish `h3` using `Nat.dvd_gcd h1 h2`. Rewrite `h3` using `[a.reduced.gcd_eq_one]`. Conclude with `hlp.one_lt.ne' (Nat.dvd_one.mp h3)`. Establish `hnum1 : ‖(a.num : ℚ_[l])‖ = 1` using `le_antisymm (Padic.norm_int_le_one _) (not_lt.mp fun h' => hnum (Padic.norm_intCast_lt_one_iff.mp h'))`.

Establish `hden : ‖(a.den : ℚ_[l])‖ = ((l : ℝ)⁻¹) ^ n`. Rewrite using `[hn, Nat.cast_pow, norm_pow, Padic.norm_p]`. Establish `ha : (a : ℚ_[l]) = (a.num : ℚ_[l]) / (a.den : ℚ_[l])`. Rewrite using `[← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]`. Rewrite `h` using `[ha, norm_div, hnum1, hden]`.

Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hlp.one_lt`. Establish `hgt : (1 : ℝ) < 1 / ((l : ℝ)⁻¹) ^ n`. Rewrite using `[inv_pow, one_div, inv_inv]`. Conclude with `one_lt_pow₀ hl1 hn0`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `h1`. Establish `ha : (a : ℚ_[l]) = (a.num : ℚ_[l])`. Establish `h` using `(Rat.den_eq_one_iff a).mp h1`. Use `norm_cast`. Conclude with `h.symm`.

Rewrite using `[ha]`. Conclude with `Padic.norm_int_le_one _`. Rewrite using `[hexp, hna, hrat]`.
-/
theorem addCharKernel : PsiKer := by
  rintro l _ t a ⟨n, hn⟩ ht
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hexp : Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) = 1 ↔ a.den = 1 := by
    rw [Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨m, hm⟩
      rw [mul_comm (m : ℂ)] at hm
      have h1 : (a : ℂ) = (m : ℂ) := mul_left_cancel₀ hI hm
      have ha : a = m := by exact_mod_cast h1
      rw [ha]
      exact Rat.den_intCast m
    · intro h1
      refine ⟨a.num, ?_⟩
      have ha : (a : ℂ) = (a.num : ℂ) := by
        have h := (Rat.den_eq_one_iff a).mp h1
        exact_mod_cast h.symm
      rw [ha]
      ring
  have hna : ‖t‖ ≤ 1 ↔ ‖(a : ℚ_[l])‖ ≤ 1 := by
    constructor
    · intro h
      have e : (a : ℚ_[l]) = t + ((a : ℚ_[l]) - t) := by ring
      rw [e]
      refine le_trans (Padic.nonarchimedean _ _) (max_le h ?_)
      rw [norm_sub_rev]
      exact ht
    · intro h
      have e : t = (t - (a : ℚ_[l])) + (a : ℚ_[l]) := by ring
      rw [e]
      exact le_trans (Padic.nonarchimedean _ _) (max_le ht h)
  have hrat : ‖(a : ℚ_[l])‖ ≤ 1 ↔ a.den = 1 := by
    constructor
    · intro h
      by_contra hd
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hn
        exact hd hn
      have hlp : l.Prime := Fact.out
      have hnum : ¬ (l : ℤ) ∣ a.num := by
        intro hdvd
        have h1 : l ∣ a.num.natAbs := Int.natCast_dvd.mp hdvd
        have h2 : l ∣ a.den := by
          rw [hn]
          exact dvd_pow_self l hn0
        have h3 := Nat.dvd_gcd h1 h2
        rw [a.reduced.gcd_eq_one] at h3
        exact hlp.one_lt.ne' (Nat.dvd_one.mp h3)
      have hnum1 : ‖(a.num : ℚ_[l])‖ = 1 :=
        le_antisymm (Padic.norm_int_le_one _)
          (not_lt.mp fun h' => hnum (Padic.norm_intCast_lt_one_iff.mp h'))
      have hden : ‖(a.den : ℚ_[l])‖ = ((l : ℝ)⁻¹) ^ n := by
        rw [hn, Nat.cast_pow, norm_pow, Padic.norm_p]
      have ha : (a : ℚ_[l]) = (a.num : ℚ_[l]) / (a.den : ℚ_[l]) := by
        rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
      rw [ha, norm_div, hnum1, hden] at h
      have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
      have hgt : (1 : ℝ) < 1 / ((l : ℝ)⁻¹) ^ n := by
        rw [inv_pow, one_div, inv_inv]
        exact one_lt_pow₀ hl1 hn0
      linarith
    · intro h1
      have ha : (a : ℚ_[l]) = (a.num : ℚ_[l]) := by
        have h := (Rat.den_eq_one_iff a).mp h1
        norm_cast
        exact h.symm
      rw [ha]
      exact Padic.norm_int_le_one _
  rw [hexp, hna, hrat]

end PI.LocDualGen.Psi
