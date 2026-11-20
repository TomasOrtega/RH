import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPowerSumsEsymmAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Finset

/- English proof (translation)
Establish `h` using `congrArg (MvPolynomial.aeval (R := ℂ) (fun x : s => (x : ℂ))) (MvPolynomial.mul_esymm_eq_sum s ℂ k)`. Simplify using `only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum, MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe, MvPolynomial.psum, MvPolynomial.aeval_X] at h`. Use `h using 4 with a _` and compare the differences between its conclusion and the goal. Rewrite using `[Finset.sum_eq_multiset_sum]`. Use `conv_lhs => rw [← Multiset.map_univ_coe s]`.

Rewrite using `[Multiset.map_map]`. Both sides reduce to the same expression.
-/
theorem multiset_mul_esymm_eq_sum (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * (s.map fun x => x ^ a.2).sum := by
  classical
  have h := congrArg (MvPolynomial.aeval (R := ℂ) (fun x : s => (x : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum s ℂ k)
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe, MvPolynomial.psum,
    MvPolynomial.aeval_X] at h
  convert h using 4 with a _
  rw [Finset.sum_eq_multiset_sum]
  conv_lhs => rw [← Multiset.map_univ_coe s]
  rw [Multiset.map_map]
  rfl

/- English proof (translation)
Introduce `σ _ V d Z hV hcard hp k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Break down `Nat.eq_zero_or_pos k with rfl | hk0` into its components or cases. Simplify `(analyticOnNhd_const (𝕜 := ℂ) (v := (1 : ℂ)) (s := V))` using `[Multiset.esymm, Multiset.powersetCard_zero_left]`.

Distinguish the cases in `hkd : d < k`. Use `(analyticOnNhd_const (𝕜 := ℂ) (v := (0 : ℂ))).congr hV fun z hz => ?_` and prove the remaining obligations. Simplify using `[Multiset.esymm, Multiset.powersetCard_eq_empty _ (by rw [hcard z hz]; exact hkd)]`. Use `push Not at hkd`. Establish `hsum : AnalyticOnNhd ℂ (fun z => ((k : ℂ))⁻¹ * ((-1) ^ (k + 1) * ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * (Z z).esymm a.1 * ((Z z).map fun x => x ^ a.2).sum)) V`.

Use `analyticOnNhd_const.mul (analyticOnNhd_const.mul ?_)` and prove the remaining obligations. Use `Finset.analyticOnNhd_fun_sum _ fun a ha => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha`. Use `(analyticOnNhd_const.mul (ih a.1 ha.2)).mul (hp a.2 (by omega) (by omega))` and prove the remaining obligations. Use `hsum.congr hV fun z _ => ?_` and prove the remaining obligations.

Rewrite using `[← multiset_mul_esymm_eq_sum, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hk0.ne'), one_mul]`.
-/
theorem PowerSumsEsymmAnalytic.proof : PowerSumsEsymmAnalytic.Statement := by
  intro σ _ V d Z hV hcard hp k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simpa [Multiset.esymm, Multiset.powersetCard_zero_left] using
      (analyticOnNhd_const (𝕜 := ℂ) (v := (1 : ℂ)) (s := V))
  by_cases hkd : d < k
  · refine (analyticOnNhd_const (𝕜 := ℂ) (v := (0 : ℂ))).congr hV fun z hz => ?_
    simp [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by rw [hcard z hz]; exact hkd)]
  push Not at hkd
  have hsum : AnalyticOnNhd ℂ (fun z => ((k : ℂ))⁻¹ * ((-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k,
        (-1) ^ a.1 * (Z z).esymm a.1 * ((Z z).map fun x => x ^ a.2).sum)) V := by
    refine analyticOnNhd_const.mul (analyticOnNhd_const.mul ?_)
    refine Finset.analyticOnNhd_fun_sum _ fun a ha => ?_
    simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
    refine (analyticOnNhd_const.mul (ih a.1 ha.2)).mul (hp a.2 (by omega) (by omega))
  refine hsum.congr hV fun z _ => ?_
  rw [← multiset_mul_esymm_eq_sum, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hk0.ne'), one_mul]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
