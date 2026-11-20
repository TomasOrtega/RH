import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.UnitPreserving

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise

noncomputable section

namespace PI.Residue

/- English proof (translation)
Rewrite using `[vfac, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow Real.pi_pos.le, ENNReal.ofReal_ofNat, ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]`.
-/
theorem vfac_eq (K : Type) [Field K] [NumberField K] :
    vfac K = ENNReal.ofReal (2 ^ nrRealPlaces K * Real.pi ^ nrComplexPlaces K) := by
  rw [vfac, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow Real.pi_pos.le, ENNReal.ofReal_ofNat, ← NNReal.coe_real_pi,
    ENNReal.ofReal_coe_nnreal]

/- English proof (translation)
Introduce `K _ _ s C hs`. Take `⟨J, hJ⟩` from `ClassGroup.mk0_surjective C⁻¹`. Use `set m := Module.finrank ℚ K with hm`. Establish `hm0 : 0 < m` using `Module.finrank_pos`. Use `set D : ℝ := ((|discr K| : ℤ) : ℝ) with hD`.

Establish `hD0 : 0 < D`. Establish `: (1 : ℤ) ≤ |discr K|` using `Int.one_le_abs (discr_ne_zero K)`. Establish `: (1 : ℝ) ≤ D` using `by rw [hD]; exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsq : 0 < √D` using `Real.sqrt_pos.mpr hD0`.

Use `set N : ℝ := (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) with hN`. Establish `hN0 : 0 < N` using `Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors J)`. Use `set P : ℝ := 2 * √D * N with hP`. Establish `hP0 : 0 < P` using `by positivity`. Use `set ρ : ℝ := P ^ ((1 : ℝ) / m) with hρ`.

Establish `hρ0 : 0 < ρ` using `Real.rpow_pos_of_pos hP0 _`. Establish `hρm : ρ ^ m = P`. Rewrite using `[hρ, ← Real.rpow_natCast, ← Real.rpow_mul hP0.le, one_div, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm0.ne'), Real.rpow_one]`. Establish `hcov : ZLattice.covolume (lat K J) = N * 2⁻¹ ^ nrComplexPlaces K * √D`. Rewrite using `[covolume_idealLattice, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, ← Int.cast_abs]`.

Establish `hcov0 : 0 < ZLattice.covolume (lat K J)` using `by rw [hcov]; positivity`. Use `set c := ENNReal.ofReal (ZLattice.covolume (lat K J)) with hc`. Establish `hc0 : c ≠ 0` using `by rw [hc]; exact (ENNReal.ofReal_pos.mpr hcov0).ne'`. Establish `hcT : c ≠ ⊤` using `ENNReal.ofReal_ne_top`. Establish `hv0 : vfac K ≠ 0`.

Rewrite using `[vfac_eq]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'`. Establish `hvT : vfac K ≠ ⊤` using `by rw [vfac_eq]; exact ENNReal.ofReal_ne_top`. Use `set S := volume (shell K) with hS`. Establish `hSe : S = vfac K * ENNReal.ofReal (regulator K) / 2` using `hSV K`. Establish `hST : S ≠ ⊤`.

Rewrite using `[hSe]`. Conclude with `ENNReal.div_ne_top (ENNReal.mul_ne_top hvT ENNReal.ofReal_ne_top) (by norm_num)`. Use `set T := ∑' x : lat K J, volume (shell K ∩ hit K ρ (x : mixedSpace K)) with hT`. Establish `h1 : vfac K * ENNReal.ofReal ((ρ / 2) ^ m) * S ≤ T * c` using `hCI K J ρ hρ0`. Establish `h2 : 2 * c ≤ vfac K * ENNReal.ofReal ((ρ / 2) ^ m)`.

Rewrite using `[vfac_eq, ← ENNReal.ofReal_mul (by positivity), hc, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[hcov, div_pow, hρm, hP, hm, ← card_add_two_mul_card_eq_rank K, pow_add, pow_mul]`. Establish `h4 : (2⁻¹ : ℝ) ^ nrComplexPlaces K ≤ (Real.pi / 4) ^ nrComplexPlaces K` using `pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) _`. Establish `e : (2 : ℝ) ^ nrRealPlaces K * Real.pi ^ nrComplexPlaces K * (2 * √D * N / (2 ^ nrRealPlaces K * (2 ^ 2) ^ nrComplexPlaces K)) = 2 * (N * (Real.pi / 4) ^ nrComplexPlaces K * √D)`.

Rewrite using `[div_pow]`. Evaluate the numerical expressions. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Use `gcongr`.

Establish `h3 : 2 * S ≤ T`. Establish `: 2 * S * c ≤ T * c`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(ENNReal.mul_le_mul_iff_left hc0 hcT).1 this`. Use `set Z : ℝ≥0∞ := ENNReal.ofReal (P * (2 * P) ^ (s - 1)) * ((torsionOrder K : ℝ≥0∞) * ENNReal.ofReal (N ^ (-s)) * classZeta K C s) with hZ`.

Establish `h4 : T ≤ S + vfac K * Z`. Use `(hU K J ρ hρ0).trans ?_` and prove the remaining obligations. Use `gcongr`. Combine the equalities or inequalities in the displayed calculation. Use `ENNReal.tsum_le_tsum fun x => ?_` and prove the remaining obligations.

Use `hH K ρ s (x : mixedSpace K) hρ0 hs (norm_pos_of_mem x.2.1)` as an intermediate fact. Rewrite `this` using `[← hm, hρm, ENNReal.ofReal_mul (by positivity)]`. Then use the resulting hypothesis. Use `_ = vfac K * (ENNReal.ofReal (P * (2 * P) ^ (s - 1)) * ∑' x : idealSet K J, ENNReal.ofReal (mixedEmbedding.norm (x : mixedSpace K) ^ (-s))) := by`. Rewrite using `[ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]`. Use `_ ≤ vfac K * Z := by`.

Rewrite using `[hZ]`. Use `gcongr`. Conclude with `hI K s C J hJ`. Establish `h5 : S ≤ vfac K * Z`. Establish `: S + S ≤ S + vfac K * Z` using `by rw [← two_mul]; exact h3.trans h4`.

Conclude with `(ENNReal.add_le_add_iff_left hST).1 this`. Establish `h6 : ENNReal.ofReal (regulator K) ≤ 2 * Z`. Rewrite `h5` using `[hSe, ENNReal.div_le_iff (by norm_num) (by norm_num), mul_assoc]`. Use `(ENNReal.mul_le_mul_iff_right hv0 hvT).1 h5` as an intermediate fact. Rewrite `this` using `[mul_comm]`. Then use the resulting hypothesis.

Use `h6.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hZ, ← mul_assoc, ← mul_assoc, ← mul_assoc]`. Use `congr 1`. Rewrite using `[show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]`. Use `congr 1`.

Establish `e1 : 2 * (P * (2 * P) ^ (s - 1)) = (2 * P) ^ s`. Rewrite using `[← mul_assoc]`. Use `nth_rewrite 1 [← Real.rpow_one (2 * P)]`. Rewrite using `[← Real.rpow_add (by positivity)]; congr 1; ring`. Establish `e2 : (2 * P) ^ s * N ^ (-s) = 4 ^ s * D ^ (s / 2)`.

Establish `: 2 * P = 4 * √D * N` using `by rw [hP]; ring`. Rewrite using `[this, Real.mul_rpow (by positivity) hN0.le, Real.mul_rpow (by norm_num) hsq.le, mul_assoc, ← Real.rpow_add hN0, add_neg_cancel, Real.rpow_zero, mul_one, Real.sqrt_eq_rpow, ← Real.rpow_mul hD0.le]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, mul_right_comm, e2]`.
-/
theorem classLower_of (hCI : CountIntegral) (hSV : ShellVolume) (hU : Unfold) (hH : HitBound)
    (hI : IdealSetSum) : ClassLower := by
  intro K _ _ s C hs
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  set m := Module.finrank ℚ K with hm
  have hm0 : 0 < m := Module.finrank_pos
  set D : ℝ := ((|discr K| : ℤ) : ℝ) with hD
  have hD0 : 0 < D := by
    have : (1 : ℤ) ≤ |discr K| := Int.one_le_abs (discr_ne_zero K)
    have : (1 : ℝ) ≤ D := by rw [hD]; exact_mod_cast this
    linarith
  have hsq : 0 < √D := Real.sqrt_pos.mpr hD0
  set N : ℝ := (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) with hN
  have hN0 : 0 < N := Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors J)
  set P : ℝ := 2 * √D * N with hP
  have hP0 : 0 < P := by positivity
  set ρ : ℝ := P ^ ((1 : ℝ) / m) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hP0 _
  have hρm : ρ ^ m = P := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hP0.le, one_div,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm0.ne'), Real.rpow_one]
  have hcov : ZLattice.covolume (lat K J) = N * 2⁻¹ ^ nrComplexPlaces K * √D := by
    rw [covolume_idealLattice, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm,
      Rat.cast_natCast, ← Int.cast_abs]
  have hcov0 : 0 < ZLattice.covolume (lat K J) := by rw [hcov]; positivity
  set c := ENNReal.ofReal (ZLattice.covolume (lat K J)) with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.mpr hcov0).ne'
  have hcT : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hv0 : vfac K ≠ 0 := by
    rw [vfac_eq]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hvT : vfac K ≠ ⊤ := by rw [vfac_eq]; exact ENNReal.ofReal_ne_top
  set S := volume (shell K) with hS
  have hSe : S = vfac K * ENNReal.ofReal (regulator K) / 2 := hSV K
  have hST : S ≠ ⊤ := by
    rw [hSe]
    exact ENNReal.div_ne_top (ENNReal.mul_ne_top hvT ENNReal.ofReal_ne_top) (by norm_num)
  set T := ∑' x : lat K J, volume (shell K ∩ hit K ρ (x : mixedSpace K)) with hT
  have h1 : vfac K * ENNReal.ofReal ((ρ / 2) ^ m) * S ≤ T * c := hCI K J ρ hρ0
  have h2 : 2 * c ≤ vfac K * ENNReal.ofReal ((ρ / 2) ^ m) := by
    rw [vfac_eq, ← ENNReal.ofReal_mul (by positivity), hc,
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [hcov, div_pow, hρm, hP, hm, ← card_add_two_mul_card_eq_rank K, pow_add, pow_mul]
    have h4 : (2⁻¹ : ℝ) ^ nrComplexPlaces K ≤ (Real.pi / 4) ^ nrComplexPlaces K :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) _
    have e : (2 : ℝ) ^ nrRealPlaces K * Real.pi ^ nrComplexPlaces K *
        (2 * √D * N / (2 ^ nrRealPlaces K * (2 ^ 2) ^ nrComplexPlaces K)) =
        2 * (N * (Real.pi / 4) ^ nrComplexPlaces K * √D) := by
      rw [div_pow]; norm_num; field_simp
    rw [e]
    gcongr
  have h3 : 2 * S ≤ T := by
    have : 2 * S * c ≤ T * c := by
      calc 2 * S * c = 2 * c * S := by ring
        _ ≤ vfac K * ENNReal.ofReal ((ρ / 2) ^ m) * S := by gcongr
        _ ≤ T * c := h1
    exact (ENNReal.mul_le_mul_iff_left hc0 hcT).1 this
  set Z : ℝ≥0∞ := ENNReal.ofReal (P * (2 * P) ^ (s - 1)) *
    ((torsionOrder K : ℝ≥0∞) * ENNReal.ofReal (N ^ (-s)) * classZeta K C s) with hZ
  have h4 : T ≤ S + vfac K * Z := by
    refine (hU K J ρ hρ0).trans ?_
    gcongr
    calc ∑' x : idealSet K J,
          volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ (x : mixedSpace K))
        ≤ ∑' x : idealSet K J, vfac K * (ENNReal.ofReal (P * (2 * P) ^ (s - 1)) *
            ENNReal.ofReal (mixedEmbedding.norm (x : mixedSpace K) ^ (-s))) := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          have := hH K ρ s (x : mixedSpace K) hρ0 hs (norm_pos_of_mem x.2.1)
          rwa [← hm, hρm, ENNReal.ofReal_mul (by positivity)] at this
      _ = vfac K * (ENNReal.ofReal (P * (2 * P) ^ (s - 1)) *
            ∑' x : idealSet K J, ENNReal.ofReal (mixedEmbedding.norm (x : mixedSpace K) ^ (-s))) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ ≤ vfac K * Z := by
          rw [hZ]; gcongr; exact hI K s C J hJ
  have h5 : S ≤ vfac K * Z := by
    have : S + S ≤ S + vfac K * Z := by rw [← two_mul]; exact h3.trans h4
    exact (ENNReal.add_le_add_iff_left hST).1 this
  have h6 : ENNReal.ofReal (regulator K) ≤ 2 * Z := by
    rw [hSe, ENNReal.div_le_iff (by norm_num) (by norm_num), mul_assoc] at h5
    have := (ENNReal.mul_le_mul_iff_right hv0 hvT).1 h5
    rwa [mul_comm] at this
  refine h6.trans (le_of_eq ?_)
  rw [hZ, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have e1 : 2 * (P * (2 * P) ^ (s - 1)) = (2 * P) ^ s := by
    rw [← mul_assoc]
    nth_rewrite 1 [← Real.rpow_one (2 * P)]
    rw [← Real.rpow_add (by positivity)]; congr 1; ring
  have e2 : (2 * P) ^ s * N ^ (-s) = 4 ^ s * D ^ (s / 2) := by
    have : 2 * P = 4 * √D * N := by rw [hP]; ring
    rw [this, Real.mul_rpow (by positivity) hN0.le, Real.mul_rpow (by norm_num) hsq.le, mul_assoc,
      ← Real.rpow_add hN0, add_neg_cancel, Real.rpow_zero, mul_one, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hD0.le]
    congr 2; ring
  rw [e1, mul_right_comm, e2]

end PI.Residue
