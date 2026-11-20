import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

open Polynomial

namespace RatDilation

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_coe]`. Proceed by induction on `f using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp [add_comp, hp, hq, mul_add]`. Consider the case `monomial m c`.

Rewrite using `[← C_mul_X_pow_eq_monomial]`. Simplify using `only [mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow]`. Apply the tactic sequence `split_ifs with h <;> simp [h, mul_comm]`.
-/
theorem coe_comp_C_mul_X {F : Type} [Field F] (a : F) (f : F[X]) :
    ((f.comp (C a * X) : F[X]) : PowerSeries F) = PowerSeries.rescale a (f : PowerSeries F) := by
  ext n
  rw [PowerSeries.coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_coe]
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial m c =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow]
    split_ifs with h <;> simp [h, mul_comm]

/- English proof (translation)
Rewrite using `[natDegree_comp, natDegree_C_mul_X _ two_ne_zero, mul_one]`.
-/
theorem natDegree_comp_two {F : Type} [Field F] [CharZero F] (f : F[X]) :
    (f.comp (C (2:F) * X)).natDegree = f.natDegree := by
  rw [natDegree_comp, natDegree_C_mul_X _ two_ne_zero, mul_one]

/- English proof (translation)
Establish `hd : f ^ 2 ∣ f.comp (C (2:F) * X)`. Establish `: f ^ 2 ∣ f.comp (C (2:F) * X) * g ^ 2` using `h ▸ dvd_mul_left _ _`. Conclude with `(hc.pow).dvd_of_dvd_mul_right this`. Establish `hne : f.comp (C (2:F) * X) ≠ 0`. Introduce `h0`.

Rewrite `h0` using `[comp_eq_zero_iff]`. Break down `h0 with h0 | ⟨_, h0⟩` into its components or cases. Conclude with `hf h0`. Use `congrArg natDegree h0` as an intermediate fact. Rewrite `this` using `[natDegree_C_mul_X _ two_ne_zero, natDegree_C]`.

Conclude with `one_ne_zero this`. Use `natDegree_le_of_dvd hd hne` as an intermediate fact. Rewrite `this` using `[natDegree_comp_two, natDegree_pow]`. Use linear arithmetic over natural numbers and integers.
-/
theorem natDegree_eq_zero_of_sq_dvd {F : Type} [Field F] [CharZero F] (f g : F[X]) (hf : f ≠ 0)
    (hc : IsCoprime f g) (h : f.comp (C (2:F) * X) * g ^ 2 = g.comp (C (2:F) * X) * f ^ 2) :
    f.natDegree = 0 := by
  have hd : f ^ 2 ∣ f.comp (C (2:F) * X) := by
    have : f ^ 2 ∣ f.comp (C (2:F) * X) * g ^ 2 := h ▸ dvd_mul_left _ _
    exact (hc.pow).dvd_of_dvd_mul_right this
  have hne : f.comp (C (2:F) * X) ≠ 0 := by
    intro h0
    rw [comp_eq_zero_iff] at h0
    rcases h0 with h0 | ⟨_, h0⟩
    · exact hf h0
    · have := congrArg natDegree h0
      rw [natDegree_C_mul_X _ two_ne_zero, natDegree_C] at this
      exact one_ne_zero this
  have := natDegree_le_of_dvd hd hne
  rw [natDegree_comp_two, natDegree_pow] at this
  omega

end RatDilation

open RatDilation in

/- English proof (translation)
Take `⟨p₀, q₀, hq₀, hpq₀⟩` from `hr`. Use `set g := GCDMonoid.gcd p₀ q₀ with hg`. Establish `hg0 : g ≠ 0` using `fun h => hq₀ ((gcd_eq_zero_iff _ _).1 h).2`. Use `set p := p₀ / g`. Use `set q := q₀ / g`.

Establish `hcop : IsCoprime p q` using `isCoprime_div_gcd_div_gcd hq₀`. Establish `hp₀ : p₀ = g * p` using `(EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left _ _)).symm`. Establish `hq₀' : q₀ = g * q` using `(EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right _ _)).symm`. Establish `hq : q ≠ 0` using `by rintro h; rw [h, mul_zero] at hq₀'; exact hq₀ hq₀'`. Establish `hgc : ((g : F[X]) : PowerSeries F) ≠ 0`.

Rewrite using `[Ne, Polynomial.coe_eq_zero_iff]` and apply the resulting hypothesis. Establish `hpq : (q : PowerSeries F) * φ = (p : PowerSeries F)`. Rewrite `hpq₀` using `[hp₀, hq₀', Polynomial.coe_mul, Polynomial.coe_mul, mul_assoc]`. Conclude with `mul_left_cancel₀ hgc hpq₀`. Establish `hφ0 : φ ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at h0`. Establish `hp : p ≠ 0`. Introduce and unpack `h`. Rewrite `hpq` using `[h, Polynomial.coe_zero]`.

Break down `mul_eq_zero.1 hpq with h' | h'` into its components or cases. Conclude with `hq ((Polynomial.coe_eq_zero_iff).1 h')`. Conclude with `hφ0 h'`. Establish `key : p.comp (C (2:F) * X) * q ^ 2 = q.comp (C (2:F) * X) * p ^ 2`. Apply `Polynomial.coe_inj.1` to reduce the goal to its premises.

Establish `e` using `congrArg (PowerSeries.rescale (2:F)) hpq`. Rewrite `e` using `[map_mul, h2, ← coe_comp_C_mul_X, ← coe_comp_C_mul_X]`. Simplify using `only [Polynomial.coe_mul, Polynomial.coe_pow]`. Rewrite using `[← e, ← hpq]`. Expand and normalize the polynomial expressions, which then agree.

Establish `dq` using `natDegree_eq_zero_of_sq_dvd q p hq hcop.symm key.symm`. Establish `dp` using `natDegree_eq_zero_of_sq_dvd p q hp hcop key`. Rewrite `hpq` using `[eq_C_of_natDegree_eq_zero dq, eq_C_of_natDegree_eq_zero dp]`. Rewrite `hpq` using `[Polynomial.coe_C, Polynomial.coe_C]`. Establish `hc` using `congrArg PowerSeries.constantCoeff hpq`.

Simplify using `only [map_mul, h0, mul_one, PowerSeries.constantCoeff_C] at hc`. Rewrite `hpq` using `[← hc]`. Establish `ha : (PowerSeries.C (q.coeff 0) : PowerSeries F) ≠ 0`. Introduce `h`. Establish `h'` using `congrArg PowerSeries.constantCoeff h`.

Rewrite `h'` using `[PowerSeries.constantCoeff_C, map_zero]`. Apply `hq` to reduce the goal to its premises. Rewrite using `[eq_C_of_natDegree_eq_zero dq, h', C_0]`. Conclude with `mul_left_cancel₀ ha (hpq.trans (mul_one _).symm)`.
-/
theorem rat_dilation_eq_one (F : Type) [Field F] [CharZero F] (φ : PowerSeries F) (hr : IsRat φ)
    (h0 : PowerSeries.constantCoeff φ = 1) (h2 : PowerSeries.rescale 2 φ = φ ^ 2) : φ = 1 := by
  classical
  obtain ⟨p₀, q₀, hq₀, hpq₀⟩ := hr
  set g := GCDMonoid.gcd p₀ q₀ with hg
  have hg0 : g ≠ 0 := fun h => hq₀ ((gcd_eq_zero_iff _ _).1 h).2
  set p := p₀ / g
  set q := q₀ / g
  have hcop : IsCoprime p q := isCoprime_div_gcd_div_gcd hq₀
  have hp₀ : p₀ = g * p := (EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left _ _)).symm
  have hq₀' : q₀ = g * q := (EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right _ _)).symm
  have hq : q ≠ 0 := by rintro h; rw [h, mul_zero] at hq₀'; exact hq₀ hq₀'
  have hgc : ((g : F[X]) : PowerSeries F) ≠ 0 := by
    rwa [Ne, Polynomial.coe_eq_zero_iff]
  have hpq : (q : PowerSeries F) * φ = (p : PowerSeries F) := by
    rw [hp₀, hq₀', Polynomial.coe_mul, Polynomial.coe_mul, mul_assoc] at hpq₀
    exact mul_left_cancel₀ hgc hpq₀
  have hφ0 : φ ≠ 0 := by
    rintro rfl; simp at h0
  have hp : p ≠ 0 := by
    rintro h
    rw [h, Polynomial.coe_zero] at hpq
    rcases mul_eq_zero.1 hpq with h' | h'
    · exact hq ((Polynomial.coe_eq_zero_iff).1 h')
    · exact hφ0 h'
  have key : p.comp (C (2:F) * X) * q ^ 2 = q.comp (C (2:F) * X) * p ^ 2 := by
    apply Polynomial.coe_inj.1
    have e := congrArg (PowerSeries.rescale (2:F)) hpq
    rw [map_mul, h2, ← coe_comp_C_mul_X, ← coe_comp_C_mul_X] at e
    simp only [Polynomial.coe_mul, Polynomial.coe_pow]
    rw [← e, ← hpq]; ring
  have dq := natDegree_eq_zero_of_sq_dvd q p hq hcop.symm key.symm
  have dp := natDegree_eq_zero_of_sq_dvd p q hp hcop key
  rw [eq_C_of_natDegree_eq_zero dq, eq_C_of_natDegree_eq_zero dp] at hpq
  rw [Polynomial.coe_C, Polynomial.coe_C] at hpq
  have hc := congrArg PowerSeries.constantCoeff hpq
  simp only [map_mul, h0, mul_one, PowerSeries.constantCoeff_C] at hc
  rw [← hc] at hpq
  have ha : (PowerSeries.C (q.coeff 0) : PowerSeries F) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    rw [PowerSeries.constantCoeff_C, map_zero] at h'
    apply hq; rw [eq_C_of_natDegree_eq_zero dq, h', C_0]
  exact mul_left_cancel₀ ha (hpq.trans (mul_one _).symm)

end GlobalTheory.Nef
