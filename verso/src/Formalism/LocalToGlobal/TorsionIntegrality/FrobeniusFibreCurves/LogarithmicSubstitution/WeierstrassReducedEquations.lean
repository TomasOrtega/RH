import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementA

noncomputable section

namespace Formalism.L2.Th1.B

open PowerSeries

section Rules

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
Rewrite using `[show (OfNat.ofNat n : PowerSeries K) = C (OfNat.ofNat n : K) from (map_ofNat C n).symm]`. Conclude with `PowerSeries.derivative_C`.
-/
theorem dz_ofNat (n : ℕ) [n.AtLeastTwo] : dz (OfNat.ofNat n : PowerSeries K) = 0 := by
  rw [show (OfNat.ofNat n : PowerSeries K) = C (OfNat.ofNat n : K) from (map_ofNat C n).symm]
  exact PowerSeries.derivative_C

/- English proof (translation)
Conclude with `Derivation.map_one_eq_zero _`.
-/
theorem dz_one : dz (1 : PowerSeries K) = 0 := by
  exact Derivation.map_one_eq_zero _

/- English proof (translation)
The claim follows from `PowerSeries.derivative_C`.
-/
theorem dz_C (a : K) : dz (C a : PowerSeries K) = 0 := PowerSeries.derivative_C

/- English proof (translation)
The claim follows from `PowerSeries.derivative_X`.
-/
theorem dz_X : dz (X : PowerSeries K) = 1 := PowerSeries.derivative_X

/- English proof (translation)
The claim follows from `map_add _ f g`.
-/
theorem dz_add (f g : PowerSeries K) : dz (f + g) = dz f + dz g := map_add _ f g

/- English proof (translation)
The claim follows from `map_sub _ f g`.
-/
theorem dz_sub (f g : PowerSeries K) : dz (f - g) = dz f - dz g := map_sub _ f g

/- English proof (translation)
The claim follows from `map_neg _ f`.
-/
theorem dz_neg (f : PowerSeries K) : dz (-f) = -dz f := map_neg _ f

/- English proof (translation)
Simplify using `only [dz, Derivation.leibniz, smul_eq_mul]`.
-/
theorem dz_mul (f g : PowerSeries K) : dz (f * g) = f * dz g + g * dz f := by
  simp only [dz, Derivation.leibniz, smul_eq_mul]

/- English proof (translation)
The claim follows from `dz_ofNat 2`.
-/
theorem dz_two : dz (2 : PowerSeries K) = 0 := dz_ofNat 2

/- English proof (translation)
The claim follows from `dz_ofNat 4`.
-/
theorem dz_four : dz (4 : PowerSeries K) = 0 := dz_ofNat 4

/- English proof (translation)
Introduce `h`. Establish `h2` using `congrArg (constantCoeff (R := K)) h`. Rewrite `h2` using `[map_ofNat, map_zero]`. Conclude with `two_ne_zero h2`.
-/
theorem two_ne : (2 : PowerSeries K) ≠ 0 := by
  intro h
  have h2 := congrArg (constantCoeff (R := K)) h
  rw [map_ofNat, map_zero] at h2
  exact two_ne_zero h2

/- English proof (translation)
Rewrite using `[pow_two, dz_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dz_sq (f : PowerSeries K) : dz (f ^ 2) = 2 * f * dz f := by
  rw [pow_two, dz_mul]
  ring

/- English proof (translation)
Rewrite using `[pow_succ, dz_mul, dz_sq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dz_cube (f : PowerSeries K) : dz (f ^ 3) = 3 * f ^ 2 * dz f := by
  rw [pow_succ, dz_mul, dz_sq]
  ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [dz_X]`. Consider the case `succ n ih`. Rewrite using `[pow_succ, dz_mul, ih, dz_X]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dz_X_pow (n : ℕ) : dz ((X : PowerSeries K) ^ (n + 1)) = ((n : PowerSeries K) + 1) * X ^ n := by
  induction n with
  | zero => simp [dz_X]
  | succ n ih =>
    rw [pow_succ, dz_mul, ih, dz_X]
    push_cast
    ring

/- English proof (translation)
The claim follows from `PowerSeries.X_ne_zero`.
-/
theorem X_ne : (X : PowerSeries K) ≠ 0 := PowerSeries.X_ne_zero

/- English proof (translation)
Introduce and unpack `rfl`. Conclude with `h (map_zero _)`.
-/
theorem ne_zero_of_constantCoeff {f : PowerSeries K} (h : constantCoeff f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact h (map_zero _)

end Rules

/- English proof (translation)
Introduce `K _ _ g2 g3 P hP`. Take `⟨_, _, hE⟩` from `hP`. Establish `E1 : X ^ 4 * dz P ^ 2 - 4 * X * dz P = 12 * P + 12 * X ^ 2 * P ^ 2 + 4 * X ^ 4 * P ^ 3 - C g2 * X ^ 2 * (1 + X ^ 2 * P) - C g3 * X ^ 4`. Apply `mul_left_cancel₀ (pow_ne_zero 2 (X_ne (K := K)))` to reduce the goal to its premises. Take the linear combination `hE`.

Use `⟨E1, ?_⟩` and prove the remaining obligations. Establish `hg : (C g2 : PowerSeries K) = 2 * C (g2 / 2)`. Rewrite using `[← map_ofNat C 2, ← map_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Rewrite `E1` using `[hg]`. Establish `d4 : dz ((X : PowerSeries K) ^ 4) = 4 * X ^ 3`. Rewrite using `[show (X : PowerSeries K) ^ 4 = (X ^ 2) ^ 2 by ring, dz_sq, dz_sq, dz_X]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdiff : 4 * X ^ 3 * dz P ^ 2 + 2 * X ^ 4 * dz P * dz (dz P) - 4 * dz P - 4 * X * dz (dz P) = 12 * dz P + 24 * X * P ^ 2 + 24 * X ^ 2 * P * dz P + 16 * X ^ 3 * P ^ 3 + 12 * X ^ 4 * P ^ 2 * dz P - 2 * C (g2 / 2) * (2 * X + 4 * X ^ 3 * P + X ^ 4 * dz P) - 4 * C g3 * X ^ 3`.

Establish `h` using `congrArg dz E1`. Establish `c12 : dz (12 : PowerSeries K) = 0` using `dz_ofNat 12`. Simplify using `only [dz_add, dz_sub, dz_mul, dz_sq, dz_cube, dz_C, dz_X, dz_two, dz_four, c12, dz_one, d4] at h`. Take the linear combination `h`. Use `mul_left_cancel₀ (?_ : (2 * X * (X ^ 3 * dz P - 2) : PowerSeries K) ≠ 0) ?_` and prove the remaining obligations.

Use `mul_ne_zero (mul_ne_zero two_ne X_ne) (ne_zero_of_constantCoeff ?_)` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X, map_ofNat]`. Evaluate the numerical expressions. Take the linear combination `X ^ 2 * hdiff - 4 * X * E1`.
-/
theorem weierstrassReducedEquations : WpReduced := by
  intro K _ _ g2 g3 P hP
  obtain ⟨_, _, hE⟩ := hP
  have E1 : X ^ 4 * dz P ^ 2 - 4 * X * dz P =
      12 * P + 12 * X ^ 2 * P ^ 2 + 4 * X ^ 4 * P ^ 3 - C g2 * X ^ 2 * (1 + X ^ 2 * P) -
        C g3 * X ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne (K := K)))
    linear_combination hE
  refine ⟨E1, ?_⟩
  have hg : (C g2 : PowerSeries K) = 2 * C (g2 / 2) := by
    rw [← map_ofNat C 2, ← map_mul]
    congr 1
    field_simp
  rw [hg] at E1
  have d4 : dz ((X : PowerSeries K) ^ 4) = 4 * X ^ 3 := by
    rw [show (X : PowerSeries K) ^ 4 = (X ^ 2) ^ 2 by ring, dz_sq, dz_sq, dz_X]
    ring
  have hdiff : 4 * X ^ 3 * dz P ^ 2 + 2 * X ^ 4 * dz P * dz (dz P) - 4 * dz P - 4 * X * dz (dz P) =
      12 * dz P + 24 * X * P ^ 2 + 24 * X ^ 2 * P * dz P + 16 * X ^ 3 * P ^ 3 +
        12 * X ^ 4 * P ^ 2 * dz P - 2 * C (g2 / 2) * (2 * X + 4 * X ^ 3 * P + X ^ 4 * dz P) -
        4 * C g3 * X ^ 3 := by
    have h := congrArg dz E1
    have c12 : dz (12 : PowerSeries K) = 0 := dz_ofNat 12
    simp only [dz_add, dz_sub, dz_mul, dz_sq, dz_cube, dz_C, dz_X, dz_two, dz_four, c12, dz_one, d4] at h
    linear_combination h
  refine mul_left_cancel₀ (?_ : (2 * X * (X ^ 3 * dz P - 2) : PowerSeries K) ≠ 0) ?_
  · refine mul_ne_zero (mul_ne_zero two_ne X_ne) (ne_zero_of_constantCoeff ?_)
    rw [map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X, map_ofNat]
    norm_num
  · linear_combination X ^ 2 * hdiff - 4 * X * E1

/- English proof (translation)
Introduce `K _ _ A kap w hw`. Take `⟨h0, h2, hE⟩` from `hw`. Establish `e1 : constantCoeff (dz w) = PowerSeries.coeff 1 w`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]`. Simplify using the standard rewrite rules.

Establish `h1 : PowerSeries.coeff 1 w = 0`. Establish `hc` using `congrArg (constantCoeff (R := K)) hE`. Simplify `hc` using `[e1, h0]`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `hd : dz w ≠ 0`.

Introduce `h`. Establish `hc` using `congrArg (PowerSeries.coeff 1) h`. Rewrite `hc` using `[PowerSeries.coeff_derivative, h2]`. Evaluate the numerical expressions using `at hc`. Establish `hdiff` using `congrArg dz hE`.

Simplify using `only [dz_sq, dz_add, dz_mul, dz_cube, dz_C, dz_four] at hdiff`. Use `mul_left_cancel₀ (mul_ne_zero two_ne hd) ?_` and prove the remaining obligations. Take the linear combination `hdiff`.
-/
theorem invertedSecondDeriv : WSecond := by
  intro K _ _ A kap w hw
  obtain ⟨h0, h2, hE⟩ := hw
  have e1 : constantCoeff (dz w) = PowerSeries.coeff 1 w := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp
  have h1 : PowerSeries.coeff 1 w = 0 := by
    have hc := congrArg (constantCoeff (R := K)) hE
    simpa [e1, h0] using hc
  refine ⟨h1, ?_⟩
  have hd : dz w ≠ 0 := by
    intro h
    have hc := congrArg (PowerSeries.coeff 1) h
    rw [PowerSeries.coeff_derivative, h2] at hc
    norm_num at hc
  have hdiff := congrArg dz hE
  simp only [dz_sq, dz_add, dz_mul, dz_cube, dz_C, dz_four] at hdiff
  refine mul_left_cancel₀ (mul_ne_zero two_ne hd) ?_
  linear_combination hdiff

/- English proof (translation)
Introduce `K _ _ A kap w hw`. Take `⟨h1, h2⟩` from `invertedSecondDeriv K A kap w hw`. Introduce `n hn`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`.

Take `⟨m, rfl⟩` from `hn`. Break down `m with _ | m` into its components or cases. Simplify using `using h1`. Establish `hk : PowerSeries.coeff (2 * m + 1) w = 0` using `ih _ (by omega) ⟨m, rfl⟩`. Establish `hsq : PowerSeries.coeff (2 * m + 1) (w ^ 2) = 0`.

Rewrite using `[pow_two, PowerSeries.coeff_mul]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce and unpack `⟨i, j⟩ hij`. Rewrite `hij` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Simplify using `only at hij`.

Break down `Nat.even_or_odd i with ⟨a, ha⟩ | hi` into its components or cases. Rewrite using `[ih j (by omega) ⟨m - a, by omega⟩, mul_zero]`. Rewrite using `[ih i (by omega) hi, zero_mul]`. Establish `e : (2 + 4 * C A * w + 6 * C kap * w ^ 2 : PowerSeries K) = C 2 + C (4 * A) * w + C (6 * kap) * w ^ 2`. Simplify using `only [map_mul, map_ofNat]`.

Establish `hc` using `congrArg (PowerSeries.coeff (2 * m + 1)) h2`. Rewrite `hc` using `[e, map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, hk, hsq, PowerSeries.coeff_C, if_neg (by omega)]`. Simplify using `only [dz, PowerSeries.coeff_derivative] at hc`. Establish `a1 : ((2 * m + 1 + 1 : ℕ) : K) + 1 ≠ 0` using `Nat.cast_add_one_ne_zero _`. Establish `a2 : ((2 * m + 1 : ℕ) : K) + 1 ≠ 0` using `Nat.cast_add_one_ne_zero _`.

Establish `hz : PowerSeries.coeff (2 * m + 1 + 1 + 1) w = 0`. Establish `hc' : PowerSeries.coeff (2 * m + 1 + 1 + 1) w * (((2 * m + 1 + 1 : ℕ) : K) + 1) * (((2 * m + 1 : ℕ) : K) + 1) = 0`. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(mul_eq_zero.mp ((mul_eq_zero.mp hc').resolve_right a2)).resolve_right a1`.

Rewrite using `[show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring]`. Conclude with `hz`.
-/
theorem invertedEven : WEven := by
  intro K _ _ A kap w hw
  obtain ⟨h1, h2⟩ := invertedSecondDeriv K A kap w hw
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨m, rfl⟩ := hn
  rcases m with _ | m
  · simpa using h1
  ·
    have hk : PowerSeries.coeff (2 * m + 1) w = 0 := ih _ (by omega) ⟨m, rfl⟩
    have hsq : PowerSeries.coeff (2 * m + 1) (w ^ 2) = 0 := by
      rw [pow_two, PowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      rintro ⟨i, j⟩ hij
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      simp only at hij
      rcases Nat.even_or_odd i with ⟨a, ha⟩ | hi
      · rw [ih j (by omega) ⟨m - a, by omega⟩, mul_zero]
      · rw [ih i (by omega) hi, zero_mul]
    have e : (2 + 4 * C A * w + 6 * C kap * w ^ 2 : PowerSeries K) =
        C 2 + C (4 * A) * w + C (6 * kap) * w ^ 2 := by
      simp only [map_mul, map_ofNat]
    have hc := congrArg (PowerSeries.coeff (2 * m + 1)) h2
    rw [e, map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, hk, hsq,
      PowerSeries.coeff_C, if_neg (by omega)] at hc
    simp only [dz, PowerSeries.coeff_derivative] at hc
    have a1 : ((2 * m + 1 + 1 : ℕ) : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
    have a2 : ((2 * m + 1 : ℕ) : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
    have hz : PowerSeries.coeff (2 * m + 1 + 1 + 1) w = 0 := by
      have hc' : PowerSeries.coeff (2 * m + 1 + 1 + 1) w * (((2 * m + 1 + 1 : ℕ) : K) + 1) *
          (((2 * m + 1 : ℕ) : K) + 1) = 0 := by
        rw [hc]
        ring
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hc').resolve_right a2)).resolve_right a1
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring]
    exact hz

/- English proof (translation)
Introduce `K _ _ g2 g3 e1 P hP he`. Take `⟨_, _, hE⟩` from `hP`. Establish `hu : constantCoeff (1 + X ^ 2 * P - C e1 * X ^ 2) ≠ 0` using `by simp`. Establish `hw : (1 + X ^ 2 * P - C e1 * X ^ 2) * wOf e1 P = X ^ 2`. Rewrite using `[wOf, mul_left_comm, PowerSeries.mul_inv_cancel _ hu, mul_one]`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[wOf]`. Simplify using the standard rewrite rules. Rewrite using `[wOf, PowerSeries.coeff_X_pow_mul']`. Simplify using `[PowerSeries.constantCoeff_inv]`.

Establish `hdu : dz (1 + X ^ 2 * P - C e1 * X ^ 2) = 2 * X * P + X ^ 2 * dz P - 2 * C e1 * X`. Simplify using `only [dz_add, dz_sub, dz_mul, dz_one, dz_C, dz_X, dz_sq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd` using `congrArg dz hw`. Rewrite `hd` using `[dz_mul, hdu, dz_sq, dz_X]`.

Establish `hA : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * dz (wOf e1 P) = -X * (X ^ 3 * dz P - 2)`. Take the linear combination `(1 + X ^ 2 * P - C e1 * X ^ 2) * hd - (2 * X * P + X ^ 2 * dz P - 2 * C e1 * X) * hw`. Establish `h1 : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 4 * wOf e1 P = X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3`. Take the linear combination `(1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 * hw`. Establish `h2 : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 4 * wOf e1 P ^ 2 = X ^ 4 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2`.

Take the linear combination `((1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 * wOf e1 P + X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2) * hw`. Establish `h3 : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 4 * wOf e1 P ^ 3 = X ^ 6 * (1 + X ^ 2 * P - C e1 * X ^ 2)`. Take the linear combination `((1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 * wOf e1 P ^ 2 + X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * wOf e1 P + X ^ 4 * (1 + X ^ 2 * P - C e1 * X ^ 2)) * hw`. Establish `hg4 : (C g2 : PowerSeries K) = 4 * C (g2 / 4)`. Rewrite using `[← map_ofNat C 4, ← map_mul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite `hE` using `[hg4]`. Establish `he' : 4 * C e1 ^ 3 - 4 * C (g2 / 4) * C e1 - C g3 = (0 : PowerSeries K)`. Establish `hc` using `congrArg (C (R := K)) he`.

Rewrite `hc` using `[map_sub, map_sub, map_mul, map_mul, map_pow, map_ofNat, map_zero, hg4]`. Take the linear combination `hc`. Rewrite using `[show (C (3 * e1) : PowerSeries K) = 3 * C e1 by rw [map_mul, map_ofNat], show (C (3 * e1 ^ 2 - g2 / 4) : PowerSeries K) = 3 * C e1 ^ 2 - C (g2 / 4) by`. Rewrite using `[map_sub, map_mul, map_pow, map_ofNat]]`. Use `mul_left_cancel₀ (pow_ne_zero 4 (ne_zero_of_constantCoeff hu)) ?_` and prove the remaining obligations.

Take the linear combination `((1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * dz (wOf e1 P) - X * (X ^ 3 * dz P - 2)) * hA - 4 * h1 - 12 * C e1 * h2 - 4 * (3 * C e1 ^ 2 - C (g2 / 4)) * h3 + X ^ 2 * hE + X ^ 8 * he'`.
-/
theorem shiftedReciprocalInverted : WOfWp := by
  intro K _ _ g2 g3 e1 P hP he
  obtain ⟨_, _, hE⟩ := hP
  have hu : constantCoeff (1 + X ^ 2 * P - C e1 * X ^ 2) ≠ 0 := by simp
  have hw : (1 + X ^ 2 * P - C e1 * X ^ 2) * wOf e1 P = X ^ 2 := by
    rw [wOf, mul_left_comm, PowerSeries.mul_inv_cancel _ hu, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [wOf]
    simp
  · rw [wOf, PowerSeries.coeff_X_pow_mul']
    simp [PowerSeries.constantCoeff_inv]
  · have hdu : dz (1 + X ^ 2 * P - C e1 * X ^ 2) = 2 * X * P + X ^ 2 * dz P - 2 * C e1 * X := by
      simp only [dz_add, dz_sub, dz_mul, dz_one, dz_C, dz_X, dz_sq]
      ring
    have hd := congrArg dz hw
    rw [dz_mul, hdu, dz_sq, dz_X] at hd

    have hA : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * dz (wOf e1 P) = -X * (X ^ 3 * dz P - 2) := by
      linear_combination (1 + X ^ 2 * P - C e1 * X ^ 2) * hd - (2 * X * P + X ^ 2 * dz P - 2 * C e1 * X) * hw
    have h1 : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 4 * wOf e1 P = X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 := by
      linear_combination (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 * hw
    have h2 : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 4 * wOf e1 P ^ 2 = X ^ 4 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 := by
      linear_combination ((1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 * wOf e1 P + X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2) * hw
    have h3 : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 4 * wOf e1 P ^ 3 = X ^ 6 * (1 + X ^ 2 * P - C e1 * X ^ 2) := by
      linear_combination ((1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 * wOf e1 P ^ 2 + X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * wOf e1 P + X ^ 4 * (1 + X ^ 2 * P - C e1 * X ^ 2)) * hw
    have hg4 : (C g2 : PowerSeries K) = 4 * C (g2 / 4) := by
      rw [← map_ofNat C 4, ← map_mul]
      congr 1
      field_simp
    rw [hg4] at hE
    have he' : 4 * C e1 ^ 3 - 4 * C (g2 / 4) * C e1 - C g3 = (0 : PowerSeries K) := by
      have hc := congrArg (C (R := K)) he
      rw [map_sub, map_sub, map_mul, map_mul, map_pow, map_ofNat, map_zero, hg4] at hc
      linear_combination hc
    rw [show (C (3 * e1) : PowerSeries K) = 3 * C e1 by rw [map_mul, map_ofNat],
      show (C (3 * e1 ^ 2 - g2 / 4) : PowerSeries K) = 3 * C e1 ^ 2 - C (g2 / 4) by
        rw [map_sub, map_mul, map_pow, map_ofNat]]
    refine mul_left_cancel₀ (pow_ne_zero 4 (ne_zero_of_constantCoeff hu)) ?_
    linear_combination ((1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * dz (wOf e1 P) - X * (X ^ 3 * dz P - 2)) * hA - 4 * h1 -
      12 * C e1 * h2 - 4 * (3 * C e1 ^ 2 - C (g2 / 4)) * h3 + X ^ 2 * hE + X ^ 8 * he'

end Formalism.L2.Th1.B
