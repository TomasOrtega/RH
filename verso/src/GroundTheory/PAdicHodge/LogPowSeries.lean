import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open PowerSeries

/- English proof (translation)
Establish `h` using `sub_dvd_pow_sub_pow (1 + Polynomial.X : Polynomial R) 1 q`. Rewrite `h` using `[one_pow, add_sub_cancel_left]`. Then use the resulting hypothesis.
-/
theorem X_dvd_one_add_X_pow_sub_one {R : Type*} [CommRing R] (q : ℕ) :
    (Polynomial.X : Polynomial R) ∣ (1 + Polynomial.X) ^ q - 1 := by
  have h := sub_dvd_pow_sub_pow (1 + Polynomial.X : Polynomial R) 1 q
  rwa [one_pow, add_sub_cancel_left] at h

/- English proof (translation)
Take `⟨g, hg⟩` from `pow_dvd_pow_of_dvd (X_dvd_one_add_X_pow_sub_one (R := R) q) n`. Rewrite using `[hg, Polynomial.coeff_X_pow_mul', if_neg (not_le.2 h)]`.
-/
theorem coeff_one_add_X_pow_sub_one_pow_of_lt {R : Type*} [CommRing R] (q : ℕ) {m n : ℕ}
    (h : m < n) : (((1 + Polynomial.X : Polynomial R) ^ q - 1) ^ n).coeff m = 0 := by
  obtain ⟨g, hg⟩ := pow_dvd_pow_of_dvd (X_dvd_one_add_X_pow_sub_one (R := R) q) n
  rw [hg, Polynomial.coeff_X_pow_mul', if_neg (not_le.2 h)]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[add_mul, one_mul, map_add]`. Break down `n with _ | n` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[coeff_succ_X_mul, coeff_mk, coeff_mk, coeff_one, if_neg n.succ_ne_zero]`.

Simplify using `[pow_succ]`.
-/
theorem one_add_X_mul_mk_neg_one_pow :
    (1 + X : ℚ⟦X⟧) * mk (fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n)) = 1 := by
  ext n
  rw [add_mul, one_mul, map_add]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_mk, coeff_mk, coeff_one, if_neg n.succ_ne_zero]
    simp [pow_succ]

/- English proof (translation)
The claim follows from `HasSubst.of_constantCoeff_zero' (by simp)`.
-/
theorem hasSubst_one_add_X_pow_sub_one (q : ℕ) : HasSubst ((1 + X : ℚ⟦X⟧) ^ q - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp)

/- English proof (translation)
Use `set U : ℚ⟦X⟧ := (1 + X) ^ q - 1 with hU`. Establish `hs : HasSubst U` using `hasSubst_one_add_X_pow_sub_one q`. Use `set G : ℚ⟦X⟧ := mk fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n)`. Establish `hG : (1 + U) * G.subst U = 1`. Establish `h` using `congrArg (substAlgHom (R := ℚ) hs) one_add_X_mul_mk_neg_one_pow`.

Rewrite `h` using `[map_mul, map_add, map_one]`. Simplify using `only [coe_substAlgHom] at h`. Rewrite `h` using `[subst_X hs]`. Then use the resulting hypothesis. Establish `h1U : 1 + U = (1 + X) ^ q` using `by rw [hU]; ring`. Apply `derivative.ext` to reduce the goal to its premises.

Establish `hd : d⁄dX ℚ ((log ℚ).subst U) = d⁄dX ℚ ((q : ℚ⟦X⟧) * log ℚ)`. Establish `hunit : IsUnit (1 + X : ℚ⟦X⟧)`. Rewrite using `[isUnit_iff_constantCoeff]`. Simplify using the standard rewrite rules. Apply `hunit.mul_left_cancel` to reduce the goal to its premises.

Rewrite using `[derivative_subst hs, deriv_log, Derivation.leibniz, deriv_log]`. Break down `q with _ | q` into its components or cases. Simplify using `[hU]`. Establish `hdU : d⁄dX ℚ U = ((q + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ q`. Rewrite using `[hU, map_sub, derivative_pow, Derivation.map_one_eq_zero, sub_zero, map_add, Derivation.map_one_eq_zero, derivative_X, zero_add, mul_one, Nat.add_sub_cancel]`.

Rewrite using `[hdU]`. Establish `hc : d⁄dX ℚ ((q + 1 : ℕ) : ℚ⟦X⟧) = 0`. Rewrite using `[← map_natCast (C (R := ℚ)), derivative_C]`. Rewrite using `[hc, smul_zero, add_zero, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_left_comm, one_add_X_mul_mk_neg_one_pow, mul_one]`. Conclude with `hd`. Establish `h0 : constantCoeff U = 0` using `by simp [hU]`. Establish `h1 : constantCoeff ((log ℚ).subst U) = 0` using `constantCoeff_subst_eq_zero h0 _ constantCoeff_log`. Rewrite using `[h1]`.

Simplify using the standard rewrite rules.
-/
theorem PowerSeries.log_subst_one_add_X_pow_sub_one (q : ℕ) :
    (log ℚ).subst ((1 + X : ℚ⟦X⟧) ^ q - 1) = (q : ℚ⟦X⟧) * log ℚ := by
  set U : ℚ⟦X⟧ := (1 + X) ^ q - 1 with hU
  have hs : HasSubst U := hasSubst_one_add_X_pow_sub_one q
  set G : ℚ⟦X⟧ := mk fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n)
  have hG : (1 + U) * G.subst U = 1 := by
    have h := congrArg (substAlgHom (R := ℚ) hs) one_add_X_mul_mk_neg_one_pow
    rw [map_mul, map_add, map_one] at h
    simp only [coe_substAlgHom] at h
    rwa [subst_X hs] at h
  have h1U : 1 + U = (1 + X) ^ q := by rw [hU]; ring
  apply derivative.ext
  · have hd : d⁄dX ℚ ((log ℚ).subst U) = d⁄dX ℚ ((q : ℚ⟦X⟧) * log ℚ) := by
      have hunit : IsUnit (1 + X : ℚ⟦X⟧) := by
        rw [isUnit_iff_constantCoeff]; simp
      apply hunit.mul_left_cancel
      rw [derivative_subst hs, deriv_log, Derivation.leibniz, deriv_log]
      rcases q with _ | q
      · simp [hU]
      · have hdU : d⁄dX ℚ U = ((q + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ q := by
          rw [hU, map_sub, derivative_pow, Derivation.map_one_eq_zero, sub_zero, map_add,
            Derivation.map_one_eq_zero, derivative_X, zero_add, mul_one, Nat.add_sub_cancel]
        rw [hdU]
        have hc : d⁄dX ℚ ((q + 1 : ℕ) : ℚ⟦X⟧) = 0 := by
          rw [← map_natCast (C (R := ℚ)), derivative_C]
        rw [hc, smul_zero, add_zero, smul_eq_mul]
        calc (1 + X) * (G.subst U * (((q + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ q))
            = ((q + 1 : ℕ) : ℚ⟦X⟧) * ((1 + X) ^ (q + 1) * G.subst U) := by ring
          _ = ((q + 1 : ℕ) : ℚ⟦X⟧) := by rw [← h1U, hG, mul_one]
          _ = (1 + X) * (((q + 1 : ℕ) : ℚ⟦X⟧) * G) := by
            rw [mul_left_comm, one_add_X_mul_mk_neg_one_pow, mul_one]
    exact hd
  · have h0 : constantCoeff U = 0 := by simp [hU]
    have h1 : constantCoeff ((log ℚ).subst U) = 0 :=
      constantCoeff_subst_eq_zero h0 _ constantCoeff_log
    rw [h1]
    simp

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem one_add_X_pow_sub_one_eq_coe (q : ℕ) :
    ((1 + X : ℚ⟦X⟧) ^ q - 1) =
      (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1 : Polynomial ℚ) : ℚ⟦X⟧) := by
  simp

/- English proof (translation)
Establish `h` using `congrArg (coeff m) (PowerSeries.log_subst_one_add_X_pow_sub_one q)`. Rewrite `h` using `[coeff_subst' (hasSubst_one_add_X_pow_sub_one q), one_add_X_pow_sub_one_eq_coe]`. Simplify using `only [← Polynomial.coe_pow, Polynomial.coeff_coe, smul_eq_mul] at h`. Rewrite `h` using `[finsum_eq_sum_of_support_subset _ (s := Finset.Icc 1 m) ?_]`. Establish `hr : coeff m ((q : ℚ⟦X⟧) * log ℚ) = q * ((-1) ^ (m - 1) / m)`.

Rewrite using `[show (q : ℚ⟦X⟧) = C (q : ℚ) from (map_natCast C q).symm, coeff_C_mul, coeff_log, if_neg (by omega), Algebra.algebraMap_self, RingHom.id_apply]`. Use `congr 2`. Rewrite using `[show m + 1 = (m - 1) + 2 by omega, pow_add]; simp`. Rewrite `h` using `[hr]`. Rewrite using `[show (-1 : ℚ) ^ (m - 1) * q / m = q * ((-1) ^ (m - 1) / m) by ring, ← h]`.

Use `Finset.sum_congr rfl fun n hn => ?_` and prove the remaining obligations. Establish `hn1 : n ≠ 0` using `by have := (Finset.mem_Icc.1 hn).1; omega`. Rewrite using `[coeff_log, if_neg hn1, Algebra.algebraMap_self, RingHom.id_apply, show n + 1 = (n - 1) + 2 by omega, pow_add]`. Simplify using the standard rewrite rules. Introduce `n hn`.

Rewrite `hn` using `[Function.mem_support]`. Rewrite using `[Finset.coe_Icc, Set.mem_Icc]`. Assume the negation of the conclusion as `hc`. Break down `Nat.lt_or_ge n 1 with h1 | h1` into its components or cases. Take `rfl : n = 0` from `by omega`.

Simplify using `at hn`. Establish `hlt : m < n` using `by omega`. Rewrite `hn` using `[coeff_one_add_X_pow_sub_one_pow_of_lt q hlt, mul_zero]`. Conclude with `hn rfl`.
-/
theorem sum_coeff_one_add_X_pow_sub_one_pow (q : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ∑ n ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (n - 1) / n *
      (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m = (-1) ^ (m - 1) * q / m := by
  have h := congrArg (coeff m) (PowerSeries.log_subst_one_add_X_pow_sub_one q)
  rw [coeff_subst' (hasSubst_one_add_X_pow_sub_one q), one_add_X_pow_sub_one_eq_coe] at h
  simp only [← Polynomial.coe_pow, Polynomial.coeff_coe, smul_eq_mul] at h
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc 1 m) ?_] at h
  · have hr : coeff m ((q : ℚ⟦X⟧) * log ℚ) = q * ((-1) ^ (m - 1) / m) := by
      rw [show (q : ℚ⟦X⟧) = C (q : ℚ) from (map_natCast C q).symm, coeff_C_mul, coeff_log,
        if_neg (by omega), Algebra.algebraMap_self, RingHom.id_apply]
      congr 2
      rw [show m + 1 = (m - 1) + 2 by omega, pow_add]; simp
    rw [hr] at h
    rw [show (-1 : ℚ) ^ (m - 1) * q / m = q * ((-1) ^ (m - 1) / m) by ring, ← h]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : n ≠ 0 := by have := (Finset.mem_Icc.1 hn).1; omega
    rw [coeff_log, if_neg hn1, Algebra.algebraMap_self, RingHom.id_apply,
      show n + 1 = (n - 1) + 2 by omega, pow_add]
    simp
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.coe_Icc, Set.mem_Icc]
    by_contra hc
    rcases Nat.lt_or_ge n 1 with h1 | h1
    · obtain rfl : n = 0 := by omega
      simp at hn
    · have hlt : m < n := by omega
      rw [coeff_one_add_X_pow_sub_one_pow_of_lt q hlt, mul_zero] at hn
      exact hn rfl

/- English proof (translation)
Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Establish `hcoe : ∀ n : ℕ, (((((1 : Polynomial ℤ) + Polynomial.X) ^ q - 1) ^ n).coeff m : ℚ) = (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m` using `fun n => by`. Rewrite using `[← eq_intCast (Int.castRingHom ℚ), ← Polynomial.coeff_map]`. Simplify using `[Polynomial.map_pow]`. Establish `hm' : (m : ℚ) ≠ 0` using `by exact_mod_cast (show m ≠ 0 by omega)`.

Simplify using `only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, hcoe]`. Establish `hdiv : ∀ n ∈ Finset.Icc 1 m, (((m.factorial / n : ℕ) : ℚ)) = m.factorial / n` using `fun n hn => by`. Establish `h1` using `(Finset.mem_Icc.1 hn)`. Rewrite using `[Nat.cast_div (Nat.dvd_factorial (by omega) h1.2) (by exact_mod_cast (show n ≠ 0 by omega))]`. Rewrite using `[Finset.sum_congr rfl fun n hn => by rw [hdiv n hn]]`.

Establish `hfac : (m.factorial : ℚ) = m * (m - 1).factorial`. Rewrite using `[← Nat.cast_mul, ← Nat.mul_factorial_pred (by omega)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun n _ => by ring` and prove the remaining obligations.

Use `_ = (-1) ^ (m - 1) * q * (m - 1).factorial := by`. Rewrite using `[sum_coeff_one_add_X_pow_sub_one_pow q hm, hfac]`. Clear the denominators using the available nonvanishing facts.
-/
theorem log_pow_coeff_int (q m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Finset.Icc 1 m, (-1 : ℤ) ^ (n - 1) *
      ((((1 : Polynomial ℤ) + Polynomial.X) ^ q - 1) ^ n).coeff m * ((m.factorial / n : ℕ) : ℤ) =
      (-1) ^ (m - 1) * q * (m - 1).factorial := by
  apply Int.cast_injective (α := ℚ)
  have hcoe : ∀ n : ℕ, (((((1 : Polynomial ℤ) + Polynomial.X) ^ q - 1) ^ n).coeff m : ℚ) =
      (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m := fun n => by
    rw [← eq_intCast (Int.castRingHom ℚ), ← Polynomial.coeff_map]
    simp [Polynomial.map_pow]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, hcoe]
  have hdiv : ∀ n ∈ Finset.Icc 1 m, (((m.factorial / n : ℕ) : ℚ)) = m.factorial / n := fun n hn => by
    have h1 := (Finset.mem_Icc.1 hn)
    rw [Nat.cast_div (Nat.dvd_factorial (by omega) h1.2) (by exact_mod_cast (show n ≠ 0 by omega))]
  rw [Finset.sum_congr rfl fun n hn => by rw [hdiv n hn]]
  have hfac : (m.factorial : ℚ) = m * (m - 1).factorial := by
    rw [← Nat.cast_mul, ← Nat.mul_factorial_pred (by omega)]
  calc ∑ n ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (n - 1) *
        ((((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m) * (m.factorial / n)
      = m.factorial * ∑ n ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (n - 1) / n *
        (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => by ring
    _ = (-1) ^ (m - 1) * q * (m - 1).factorial := by
        rw [sum_coeff_one_add_X_pow_sub_one_pow q hm, hfac]
        field_simp

end GroundTheory.PAdicHodge
