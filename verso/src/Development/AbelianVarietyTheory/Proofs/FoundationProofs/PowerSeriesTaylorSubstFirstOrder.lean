import Mathlib

open Polynomial

namespace GlobalTheory

namespace TaylorSubst

variable {k : Type} [Field k]

/- English proof (translation)
Establish `hs` using `PowerSeries.HasSubst.of_constantCoeff_zero' hu`. Use `conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const χ]`. Rewrite using `[PowerSeries.subst_add hs, PowerSeries.subst_mul hs, PowerSeries.subst_X hs, PowerSeries.subst_C]`. Both sides reduce to the same expression.
-/
theorem subst_decomp (χ u : PowerSeries k) (hu : PowerSeries.constantCoeff u = 0) :
    (χ.subst u : PowerSeries k) =
      u * ((PowerSeries.mk fun p => PowerSeries.coeff (p + 1) χ).subst u : PowerSeries k)
        + PowerSeries.C (PowerSeries.constantCoeff χ) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hu
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const χ]
  rw [PowerSeries.subst_add hs, PowerSeries.subst_mul hs, PowerSeries.subst_X hs,
    PowerSeries.subst_C]
  rfl

/- English proof (translation)
Rewrite using `[subst_decomp χ u hu]`. Simplify using `[hu]`.
-/
theorem constantCoeff_subst_eq (χ u : PowerSeries k) (hu : PowerSeries.constantCoeff u = 0) :
    PowerSeries.constantCoeff (χ.subst u : PowerSeries k) = PowerSeries.constantCoeff χ := by
  rw [subst_decomp χ u hu]
  simp [hu]

/- English proof (translation)
Rewrite using `[PowerSeries.X_pow_dvd_iff]`. Introduce `i hi`. Simplify using `[Polynomial.coeff_coe, PowerSeries.coeff_trunc, hi]`.
-/
theorem X_pow_dvd_sub_trunc (χ : PowerSeries k) (n : ℕ) :
    (PowerSeries.X : PowerSeries k) ^ n ∣ χ - (PowerSeries.trunc n χ : PowerSeries k) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro i hi
  simp [Polynomial.coeff_coe, PowerSeries.coeff_trunc, hi]

/- English proof (translation)
Establish `hsu` using `PowerSeries.HasSubst.of_constantCoeff_zero' hu`. Establish `hsv` using `PowerSeries.HasSubst.of_constantCoeff_zero' hv`. Take `⟨ρ, hρ⟩` from `X_pow_dvd_sub_trunc χ n`. Establish `hχ : χ = (PowerSeries.trunc n χ : PowerSeries k) + PowerSeries.X ^ n * ρ`. Rewrite using `[← hρ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hχ, PowerSeries.subst_add hsu, PowerSeries.subst_add hsv, PowerSeries.subst_mul hsu, PowerSeries.subst_mul hsv, PowerSeries.subst_pow hsu, PowerSeries.subst_pow hsv, PowerSeries.subst_X hsu, PowerSeries.subst_X hsv, PowerSeries.subst_coe hsu, PowerSeries.subst_coe hsv]`. Establish `hXu : (PowerSeries.X : PowerSeries k) ∣ u` using `PowerSeries.X_dvd_iff.mpr hu`. Establish `hXv : (PowerSeries.X : PowerSeries k) ∣ v` using `PowerSeries.X_dvd_iff.mpr hv`. Establish `h1 : (PowerSeries.X : PowerSeries k) ^ n ∣ (Polynomial.aeval u (PowerSeries.trunc n χ) : PowerSeries k) - Polynomial.aeval v (PowerSeries.trunc n χ)`.

Use `dvd_trans huv ?_` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_def, Polynomial.aeval_def, ← Polynomial.eval_map, ← Polynomial.eval_map]`. Conclude with `Polynomial.sub_dvd_eval_sub u v _`. Establish `h2 : (PowerSeries.X : PowerSeries k) ^ n ∣ u ^ n * (ρ.subst u : PowerSeries k) - v ^ n * (ρ.subst v : PowerSeries k)` using `dvd_sub (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hXu n) _) (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hXv n) _)`. Use `dvd_add h1 h2` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem X_pow_dvd_subst_sub (χ u v : PowerSeries k) (n : ℕ)
    (hu : PowerSeries.constantCoeff u = 0) (hv : PowerSeries.constantCoeff v = 0)
    (huv : (PowerSeries.X : PowerSeries k) ^ n ∣ u - v) :
    (PowerSeries.X : PowerSeries k) ^ n ∣
      (χ.subst u : PowerSeries k) - (χ.subst v : PowerSeries k) := by
  have hsu := PowerSeries.HasSubst.of_constantCoeff_zero' hu
  have hsv := PowerSeries.HasSubst.of_constantCoeff_zero' hv
  obtain ⟨ρ, hρ⟩ := X_pow_dvd_sub_trunc χ n
  have hχ : χ = (PowerSeries.trunc n χ : PowerSeries k) + PowerSeries.X ^ n * ρ := by
    rw [← hρ]; ring
  rw [hχ, PowerSeries.subst_add hsu, PowerSeries.subst_add hsv, PowerSeries.subst_mul hsu,
    PowerSeries.subst_mul hsv, PowerSeries.subst_pow hsu, PowerSeries.subst_pow hsv,
    PowerSeries.subst_X hsu, PowerSeries.subst_X hsv, PowerSeries.subst_coe hsu,
    PowerSeries.subst_coe hsv]
  have hXu : (PowerSeries.X : PowerSeries k) ∣ u := PowerSeries.X_dvd_iff.mpr hu
  have hXv : (PowerSeries.X : PowerSeries k) ∣ v := PowerSeries.X_dvd_iff.mpr hv
  have h1 : (PowerSeries.X : PowerSeries k) ^ n ∣
      (Polynomial.aeval u (PowerSeries.trunc n χ) : PowerSeries k)
        - Polynomial.aeval v (PowerSeries.trunc n χ) := by
    refine dvd_trans huv ?_
    rw [Polynomial.aeval_def, Polynomial.aeval_def, ← Polynomial.eval_map, ← Polynomial.eval_map]
    exact Polynomial.sub_dvd_eval_sub u v _
  have h2 : (PowerSeries.X : PowerSeries k) ^ n ∣
      u ^ n * (ρ.subst u : PowerSeries k) - v ^ n * (ρ.subst v : PowerSeries k) :=
    dvd_sub (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hXu n) _)
      (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hXv n) _)
  have := dvd_add h1 h2
  convert this using 1
  ring

end TaylorSubst

/- English proof (translation)
Introduce `k _ φ a b m hm ha`. Use `⟨TaylorSubst.constantCoeff_subst_eq φ a ha, ?_⟩` and prove the remaining obligations. Use `set ψ : PowerSeries k := PowerSeries.mk fun p => PowerSeries.coeff (p + 1) φ with hψ`. Establish `ha' : PowerSeries.constantCoeff (a + PowerSeries.X ^ m * b) = 0`. Take `⟨j, rfl⟩ : ∃ j, m = j + 1` from `⟨m - 1, by omega⟩`.

Simplify using `[ha, pow_succ]`. Rewrite using `[TaylorSubst.subst_decomp φ _ ha', TaylorSubst.subst_decomp φ _ ha]`. Rewrite using `[← hψ]`. Establish `hψ0 : PowerSeries.constantCoeff ψ = PowerSeries.coeff 1 φ`. Rewrite using `[hψ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]`.

Establish `hA : (PowerSeries.X : PowerSeries k) ∣ b * (ψ.subst (a + PowerSeries.X ^ m * b) : PowerSeries k) - PowerSeries.C (PowerSeries.constantCoeff b * PowerSeries.coeff 1 φ)`. Rewrite using `[PowerSeries.X_dvd_iff, map_sub, map_mul, TaylorSubst.constantCoeff_subst_eq ψ _ ha', hψ0, PowerSeries.constantCoeff_C, sub_self]`. Establish `hB : (PowerSeries.X : PowerSeries k) ^ m ∣ (ψ.subst (a + PowerSeries.X ^ m * b) : PowerSeries k) - ψ.subst a` using `TaylorSubst.X_pow_dvd_subst_sub ψ _ a m ha' ha (by simp)`. Establish `hXa : (PowerSeries.X : PowerSeries k) ∣ a` using `PowerSeries.X_dvd_iff.mpr ha`. Establish `h` using `dvd_add (mul_dvd_mul_left ((PowerSeries.X : PowerSeries k) ^ m) hA) (mul_dvd_mul hB hXa)`.

Rewrite `h` using `[← pow_succ]`. Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem taylor_subst_first_order : ∀ (k : Type) [Field k] (φ a b : PowerSeries k) (m : ℕ), 1 ≤ m → PowerSeries.constantCoeff a = 0 →
 PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ ∧
 (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ (φ.subst (a + PowerSeries.X ^ m * b) : PowerSeries k) - φ.subst a - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff b * PowerSeries.coeff 1 φ) := by
  intro k _ φ a b m hm ha
  refine ⟨TaylorSubst.constantCoeff_subst_eq φ a ha, ?_⟩
  set ψ : PowerSeries k := PowerSeries.mk fun p => PowerSeries.coeff (p + 1) φ with hψ
  have ha' : PowerSeries.constantCoeff (a + PowerSeries.X ^ m * b) = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    simp [ha, pow_succ]
  rw [TaylorSubst.subst_decomp φ _ ha', TaylorSubst.subst_decomp φ _ ha]
  rw [← hψ]
  have hψ0 : PowerSeries.constantCoeff ψ = PowerSeries.coeff 1 φ := by
    rw [hψ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  have hA : (PowerSeries.X : PowerSeries k) ∣
      b * (ψ.subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
        - PowerSeries.C (PowerSeries.constantCoeff b * PowerSeries.coeff 1 φ) := by
    rw [PowerSeries.X_dvd_iff, map_sub, map_mul, TaylorSubst.constantCoeff_subst_eq ψ _ ha',
      hψ0, PowerSeries.constantCoeff_C, sub_self]
  have hB : (PowerSeries.X : PowerSeries k) ^ m ∣
      (ψ.subst (a + PowerSeries.X ^ m * b) : PowerSeries k) - ψ.subst a :=
    TaylorSubst.X_pow_dvd_subst_sub ψ _ a m ha' ha (by simp)
  have hXa : (PowerSeries.X : PowerSeries k) ∣ a := PowerSeries.X_dvd_iff.mpr ha
  have h := dvd_add (mul_dvd_mul_left ((PowerSeries.X : PowerSeries k) ^ m) hA)
    (mul_dvd_mul hB hXa)
  rw [← pow_succ] at h
  convert h using 1
  ring

end GlobalTheory
