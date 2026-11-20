import Mathlib
import GroundTheory.PAdicHodge.BdRSeries
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open PowerSeries

section Formal

/- English proof (translation)
Establish `hS : HasSubst (log ℚ)` using `HasSubst.log`. Use `set F : ℚ⟦X⟧ := (exp ℚ).subst (log ℚ) with hF`. Use `set G : ℚ⟦X⟧ := mk (fun n => algebraMap ℚ ℚ ((-1) ^ n)) with hG`. Establish `h1 : (1 + X : ℚ⟦X⟧) * G = 1` using `one_add_X_mul_geom`. Establish `hF' : d⁄dX ℚ F = F * G`.

Rewrite using `[hF, derivative_subst hS, derivative_exp, deriv_log]`. Establish `hG' : d⁄dX ℚ G = -(G * G)`. Establish `h` using `congrArg (d⁄dX ℚ) h1`. Rewrite `h` using `[Derivation.leibniz, derivative_one, map_add, derivative_one, derivative_X, zero_add, smul_eq_mul, smul_eq_mul, mul_one]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, mul_comm G, h1, one_mul]`. Use `_ = -(G * G) := by`. Rewrite using `[show (1 + X) * d⁄dX ℚ G = -G from eq_neg_of_add_eq_zero_left h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : constantCoeff F = 1`.

Establish `h0 : MvPowerSeries.constantCoeff (log ℚ) = 0` using `constantCoeff_log`. Establish `hz` using `constantCoeff_subst_eq_zero h0 (exp ℚ - 1) (by simp [constantCoeff_exp])`. Establish `hsub : (exp ℚ - 1 : ℚ⟦X⟧).subst (log ℚ) = F - 1`. Rewrite using `[hF, ← coe_substAlgHom hS, map_sub, map_one]`. Rewrite `hz` using `[hsub, map_sub, map_one, sub_eq_zero]`.

Conclude with `hz`. Establish `hGc : constantCoeff G = 1`. Rewrite using `[hG, ← coeff_zero_eq_constantCoeff_apply, coeff_mk]`. Simplify using the standard rewrite rules. Establish `hH : F * G = 1`.

Apply `derivative.ext` to reduce the goal to its premises. Rewrite using `[Derivation.leibniz, hF', hG', derivative_one, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, hc, hGc, map_one, mul_one]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exp_subst_log : (exp ℚ).subst (log ℚ) = (1 + X : ℚ⟦X⟧) := by
  have hS : HasSubst (log ℚ) := HasSubst.log
  set F : ℚ⟦X⟧ := (exp ℚ).subst (log ℚ) with hF
  set G : ℚ⟦X⟧ := mk (fun n => algebraMap ℚ ℚ ((-1) ^ n)) with hG
  have h1 : (1 + X : ℚ⟦X⟧) * G = 1 := one_add_X_mul_geom
  have hF' : d⁄dX ℚ F = F * G := by
    rw [hF, derivative_subst hS, derivative_exp, deriv_log]
  have hG' : d⁄dX ℚ G = -(G * G) := by
    have h := congrArg (d⁄dX ℚ) h1
    rw [Derivation.leibniz, derivative_one, map_add, derivative_one, derivative_X, zero_add,
      smul_eq_mul, smul_eq_mul, mul_one] at h
    calc d⁄dX ℚ G = G * ((1 + X) * d⁄dX ℚ G) := by
          rw [← mul_assoc, mul_comm G, h1, one_mul]
      _ = -(G * G) := by
          rw [show (1 + X) * d⁄dX ℚ G = -G from eq_neg_of_add_eq_zero_left h]
          ring
  have hc : constantCoeff F = 1 := by
    have h0 : MvPowerSeries.constantCoeff (log ℚ) = 0 := constantCoeff_log
    have hz := constantCoeff_subst_eq_zero h0 (exp ℚ - 1) (by simp [constantCoeff_exp])
    have hsub : (exp ℚ - 1 : ℚ⟦X⟧).subst (log ℚ) = F - 1 := by
      rw [hF, ← coe_substAlgHom hS, map_sub, map_one]
    rw [hsub, map_sub, map_one, sub_eq_zero] at hz
    exact hz
  have hGc : constantCoeff G = 1 := by
    rw [hG, ← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    simp
  have hH : F * G = 1 := by
    apply derivative.ext
    · rw [Derivation.leibniz, hF', hG', derivative_one, smul_eq_mul, smul_eq_mul]
      ring
    · rw [map_mul, hc, hGc, map_one, mul_one]
  calc F = F * ((1 + X) * G) := by rw [h1, mul_one]
    _ = (F * G) * (1 + X) := by ring
    _ = 1 + X := by rw [hH, one_mul]

end Formal

section Nilpotent

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/- English proof (translation)
Take `⟨h, rfl⟩` from `X_dvd_iff.2 hg`. Rewrite using `[← map_pow, mul_pow, map_mul, map_pow, truncEval_X, hs, zero_mul]`.
-/
theorem truncEval_pow_eq_zero {n : ℕ} {s : S} (hs : s ^ n = 0) {g : ℚ⟦X⟧}
    (hg : constantCoeff g = 0) : (truncEval s hs g) ^ n = 0 := by
  obtain ⟨h, rfl⟩ := X_dvd_iff.2 hg
  rw [← map_pow, mul_pow, map_mul, map_pow, truncEval_X, hs, zero_mul]

/- English proof (translation)
Establish `hS` using `HasSubst.of_constantCoeff_zero' hg`. Establish `key` using `truncEval_unique ((truncEval s hs).comp (substAlgHom hS)) (truncEval s hs g) (truncEval_pow_eq_zero hs hg) (by rw [AlgHom.comp_apply, coe_substAlgHom, subst_X hS])`. Rewrite using `[← key, AlgHom.comp_apply, coe_substAlgHom]`.
-/
theorem truncEval_subst {n : ℕ} {s : S} (hs : s ^ n = 0) {g : ℚ⟦X⟧} (hg : constantCoeff g = 0)
    (f : ℚ⟦X⟧) :
    truncEval s hs (f.subst g) = truncEval (truncEval s hs g) (truncEval_pow_eq_zero hs hg) f := by
  have hS := HasSubst.of_constantCoeff_zero' hg
  have key := truncEval_unique ((truncEval s hs).comp (substAlgHom hS)) (truncEval s hs g)
    (truncEval_pow_eq_zero hs hg) (by rw [AlgHom.comp_apply, coe_substAlgHom, subst_X hS])
  rw [← key, AlgHom.comp_apply, coe_substAlgHom]

/- English proof (translation)
Rewrite using `[truncEval_eq_sum, IsNilpotent.exp_eq_sum hs]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_exp, Algebra.smul_def, one_div]`. Simplify using the standard rewrite rules.
-/
theorem truncEval_exp {n : ℕ} {s : S} (hs : s ^ n = 0) :
    truncEval s hs (exp ℚ) = IsNilpotent.exp s := by
  rw [truncEval_eq_sum, IsNilpotent.exp_eq_sum hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_exp, Algebra.smul_def, one_div]
  simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨n, truncEval_pow_eq_zero hs constantCoeff_log⟩`.
-/
theorem isNilpotent_truncEval_log {n : ℕ} {s : S} (hs : s ^ n = 0) :
    IsNilpotent (truncEval s hs (log ℚ)) :=
  ⟨n, truncEval_pow_eq_zero hs constantCoeff_log⟩

/- English proof (translation)
Rewrite using `[← truncEval_exp (truncEval_pow_eq_zero hs constantCoeff_log), ← truncEval_subst hs (g := log ℚ) constantCoeff_log, exp_subst_log, map_add, map_one, truncEval_X]`.
-/
theorem exp_truncEval_log {n : ℕ} {s : S} (hs : s ^ n = 0) :
    IsNilpotent.exp (truncEval s hs (log ℚ)) = 1 + s := by
  rw [← truncEval_exp (truncEval_pow_eq_zero hs constantCoeff_log),
    ← truncEval_subst hs (g := log ℚ) constantCoeff_log,
    exp_subst_log, map_add, map_one, truncEval_X]

/- English proof (translation)
Take `⟨k, hk⟩` from `hc`. Use `set w : S := ∑ i ∈ Finset.range k, ((i + 1).factorial : ℚ)⁻¹ • c ^ i with hw`. Establish `hexp : IsNilpotent.exp c = 1 + c * w`. Rewrite using `[IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_succ k) hk), Finset.sum_range_succ', hw, Finset.mul_sum]`. Simplify using `only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]`.

Rewrite using `[add_comm]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, pow_succ, mul_comm c]`. Establish `hw1 : IsUnit w`.

Break down `k with _ | k` into its components or cases. Establish `: Subsingleton S` using `subsingleton_of_zero_eq_one (by simpa using hk.symm)`. Conclude with `isUnit_of_subsingleton w`. Establish `hsplit : w = 1 + c * ∑ i ∈ Finset.range k, ((i + 2).factorial : ℚ)⁻¹ • c ^ i`. Rewrite using `[hw, Finset.sum_range_succ', Finset.mul_sum]`.

Simplify using `only [pow_zero, zero_add, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]`. Rewrite using `[add_comm]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, pow_succ, mul_comm c]`.

Rewrite using `[hsplit]`. Conclude with `IsNilpotent.isUnit_one_add ⟨k + 1, by rw [mul_pow, hk, zero_mul]⟩`. Establish `h0 : c * w = 0`. Use `hexp.symm.trans h` as an intermediate fact. Rewrite `this` using `[add_eq_left]`. Then use the resulting hypothesis.

Simplify using `using (hw1.mul_left_eq_zero).1 h0`.
-/
theorem eq_zero_of_exp_eq_one {c : S} (hc : IsNilpotent c) (h : IsNilpotent.exp c = 1) : c = 0 := by
  obtain ⟨k, hk⟩ := hc
  set w : S := ∑ i ∈ Finset.range k, ((i + 1).factorial : ℚ)⁻¹ • c ^ i with hw
  have hexp : IsNilpotent.exp c = 1 + c * w := by
    rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_succ k) hk), Finset.sum_range_succ',
      hw, Finset.mul_sum]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, pow_succ, mul_comm c]
  have hw1 : IsUnit w := by
    rcases k with _ | k
    · have : Subsingleton S := subsingleton_of_zero_eq_one (by simpa using hk.symm)
      exact isUnit_of_subsingleton w
    · have hsplit : w = 1 + c * ∑ i ∈ Finset.range k, ((i + 2).factorial : ℚ)⁻¹ • c ^ i := by
        rw [hw, Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_zero, zero_add, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_smul_comm, pow_succ, mul_comm c]
      rw [hsplit]
      exact IsNilpotent.isUnit_one_add ⟨k + 1, by rw [mul_pow, hk, zero_mul]⟩
  have h0 : c * w = 0 := by
    have := hexp.symm.trans h
    rwa [add_eq_left] at this
  simpa using (hw1.mul_left_eq_zero).1 h0

/- English proof (translation)
Establish `hnb : IsNilpotent (-b)` using `hb.neg`. Establish `h1 : IsNilpotent.exp (a + -b) = 1`. Rewrite using `[IsNilpotent.exp_add_of_commute (Commute.all _ _) ha hnb, h, IsNilpotent.exp_mul_exp_neg_self hb]`. Establish `h2` using `eq_zero_of_exp_eq_one (Commute.isNilpotent_add (Commute.all _ _) ha hnb) h1`. Rewrite `h2` using `[← sub_eq_add_neg, sub_eq_zero]`.

Conclude with `h2`.
-/
theorem eq_of_exp_eq {a b : S} (ha : IsNilpotent a) (hb : IsNilpotent b)
    (h : IsNilpotent.exp a = IsNilpotent.exp b) : a = b := by
  have hnb : IsNilpotent (-b) := hb.neg
  have h1 : IsNilpotent.exp (a + -b) = 1 := by
    rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) ha hnb, h,
      IsNilpotent.exp_mul_exp_neg_self hb]
  have h2 := eq_zero_of_exp_eq_one (Commute.isNilpotent_add (Commute.all _ _) ha hnb) h1
  rw [← sub_eq_add_neg, sub_eq_zero] at h2
  exact h2

/- English proof (translation)
Establish `hnx` using `isNilpotent_truncEval_log hx`. Establish `hny` using `isNilpotent_truncEval_log hy`. Apply `eq_of_exp_eq (isNilpotent_truncEval_log hz) (Commute.isNilpotent_add (Commute.all _ _) hnx hny)` to reduce the goal to its premises. Rewrite using `[IsNilpotent.exp_add_of_commute (Commute.all _ _) hnx hny, exp_truncEval_log, exp_truncEval_log, exp_truncEval_log, hxyz]`.
-/
theorem truncEval_log_mul {l m n : ℕ} {x y z : S} (hx : x ^ l = 0) (hy : y ^ m = 0)
    (hz : z ^ n = 0) (hxyz : 1 + z = (1 + x) * (1 + y)) :
    truncEval z hz (log ℚ) = truncEval x hx (log ℚ) + truncEval y hy (log ℚ) := by
  have hnx := isNilpotent_truncEval_log hx
  have hny := isNilpotent_truncEval_log hy
  apply eq_of_exp_eq (isNilpotent_truncEval_log hz) (Commute.isNilpotent_add (Commute.all _ _) hnx hny)
  rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) hnx hny, exp_truncEval_log,
    exp_truncEval_log, exp_truncEval_log, hxyz]

end Nilpotent

section Complete

variable {B : Type*} [CommRing B] [Algebra ℚ B] {I : Ideal B} [IsAdicComplete I B]

/- English proof (translation)
The claim follows from `IsAdicComplete.mk_liftAlgHom I (fun n => truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n)) (fun hle => factorₐ_comp_truncEval I hz hle) n f`.
-/
theorem mk_seriesEval_eq_truncEval {z : B} (hz : z ∈ I) (f : ℚ⟦X⟧) (n : ℕ) :
    Ideal.Quotient.mk (I ^ n) (seriesEval I z hz f) =
      truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n) f :=
  IsAdicComplete.mk_liftAlgHom I
    (fun n => truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n))
    (fun hle => factorₐ_comp_truncEval I hz hle) n f

/- English proof (translation)
Use `eq_of_forall_sub_mem_pow I fun n => ?_` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq, map_add, logOnePlus, logOnePlus, logOnePlus, mk_seriesEval_eq_truncEval, mk_seriesEval_eq_truncEval, mk_seriesEval_eq_truncEval]`. Conclude with `truncEval_log_mul _ _ _ (by rw [← map_one (Ideal.Quotient.mk (I ^ n)), ← map_add, hxyz, map_mul, map_add, map_add, map_one])`.
-/
theorem logOnePlus_mul {x y z : B} (hx : x ∈ I) (hy : y ∈ I) (hz : z ∈ I)
    (hxyz : 1 + z = (1 + x) * (1 + y)) :
    logOnePlus I z hz = logOnePlus I x hx + logOnePlus I y hy := by
  refine eq_of_forall_sub_mem_pow I fun n => ?_
  rw [← Ideal.Quotient.eq, map_add, logOnePlus, logOnePlus, logOnePlus,
    mk_seriesEval_eq_truncEval, mk_seriesEval_eq_truncEval, mk_seriesEval_eq_truncEval]
  exact truncEval_log_mul _ _ _ (by rw [← map_one (Ideal.Quotient.mk (I ^ n)), ← map_add, hxyz,
    map_mul, map_add, map_add, map_one])

end Complete

end GroundTheory.PAdicHodge
