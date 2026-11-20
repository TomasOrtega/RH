import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenOfPoincareLelongHyperplane
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LogInt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenCoord
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HasCompactSupportCompHypInclAt

namespace ReciprocityTheory.AnForm.A

open MeasureTheory Filter Topology

/- English proof (translation)
Introduce `n U v φ hp`. Establish `hf : (hypInclAt (n` using `n) 0) = hypIncl := funext hypInclAt_zero`. Establish `h` using `log_norm_integral_at_coordinate n 0 U v φ hp`. Unfold `densHypAt at h`. Rewrite `h` using `[hf]`.

Conclude with `h`.
-/
theorem log_norm_integral_formula : PoincareLelongHyperplane := by
  intro n U v φ hp
  have hf : (hypInclAt (n := n) 0) = hypIncl := funext hypInclAt_zero
  have h := log_norm_integral_at_coordinate n 0 U v φ hp
  unfold densHypAt at h
  rw [hf] at h
  exact h

/- English proof (translation)
Introduce `n m U v φ u hp hu hu0`. Take `⟨-, -, -, hsub, -⟩` from `id hp`. Take `⟨hI1, -, hE1⟩` from `log_norm_integral_formula n U v φ hp`. Take `⟨hI2, hE2⟩` from `unit_part hp hu hu0`. Establish `hae : (fun z : Fin (n + 1) → ℂ => Real.log ‖z 0 ^ m * u z‖ * densV v φ z) =ᵐ[volume] fun z => (m : ℝ) * (Real.log ‖z 0‖ * densV v φ z) + Real.log ‖u z‖ * densV v φ z` using `by filter_upwards [ae_coord_ne_zero (0 : Fin (n + 1))] with z hz`.

Distinguish the cases in `hzv : z ∈ tsupport v`. Establish `huz : u z ≠ 0` using `hu0 z (hsub hzv)`. Rewrite using `[norm_mul, norm_zpow, Real.log_mul (zpow_ne_zero _ (norm_ne_zero_iff.mpr hz)) (norm_ne_zero_iff.mpr huz), Real.log_zpow]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : densV v φ z = 0` using `maDens_cons_eq_zero φ hzv`.

Rewrite using `[h0]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨((hI1.const_mul (m : ℝ)).add hI2).congr hae.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_congr_ae hae, integral_add (hI1.const_mul _) hI2]`. Use `first`.

Consider the case `rw [integral_const_mul]`. Consider the case `rw [integral_mul_left]`. Rewrite using `[hE1, hE2, add_zero]`.
-/
theorem log_norm_integral_formula_unit : PoincareLelongUnitPower := by
  intro n m U v φ u hp hu hu0
  obtain ⟨-, -, -, hsub, -⟩ := id hp
  obtain ⟨hI1, -, hE1⟩ := log_norm_integral_formula n U v φ hp
  obtain ⟨hI2, hE2⟩ := unit_part hp hu hu0
  have hae : (fun z : Fin (n + 1) → ℂ => Real.log ‖z 0 ^ m * u z‖ * densV v φ z) =ᵐ[volume]
      fun z => (m : ℝ) * (Real.log ‖z 0‖ * densV v φ z) + Real.log ‖u z‖ * densV v φ z := by
    filter_upwards [ae_coord_ne_zero (0 : Fin (n + 1))] with z hz
    by_cases hzv : z ∈ tsupport v
    · have huz : u z ≠ 0 := hu0 z (hsub hzv)
      rw [norm_mul, norm_zpow, Real.log_mul (zpow_ne_zero _ (norm_ne_zero_iff.mpr hz))
        (norm_ne_zero_iff.mpr huz), Real.log_zpow]
      ring
    · have h0 : densV v φ z = 0 := maDens_cons_eq_zero φ hzv
      rw [h0]
      ring
  refine ⟨((hI1.const_mul (m : ℝ)).add hI2).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_add (hI1.const_mul _) hI2]
  first
    | rw [integral_const_mul]
    | rw [integral_mul_left]
  rw [hE1, hE2, add_zero]

/- English proof (translation)
Introduce `n m U v φ u hp hu hu0`. Take `⟨-, -, -, hsub, -⟩` from `id hp`. Establish `hI : ∀ i, Integrable (fun z : Fin (n + 1) → ℂ => Real.log ‖z i‖ * densV v φ z) volume` using `fun i => (log_norm_integral_at_coordinate n i U v φ hp).1`. Establish `hE : ∀ i, ∫ z, Real.log ‖z i‖ * densV v φ z = ∫ w, v (hypInclAt i w) * densHypAt i φ w` using `fun i => (log_norm_integral_at_coordinate n i U v φ hp).2.2`. Take `⟨hIu, hEu⟩` from `unit_part hp hu hu0`.

Establish `hIs : Integrable (fun z : Fin (n + 1) → ℂ => ∑ i ∈ Finset.univ, (m i : ℝ) * (Real.log ‖z i‖ * densV v φ z)) volume` using `integrable_finset_sum Finset.univ (fun i _ => (hI i).const_mul (m i : ℝ))`. Establish `hae : (fun z : Fin (n + 1) → ℂ => Real.log ‖u z * ∏ i, z i ^ m i‖ * densV v φ z) =ᵐ[volume] fun z => Real.log ‖u z‖ * densV v φ z + ∑ i ∈ Finset.univ, (m i : ℝ) * (Real.log ‖z i‖ * densV v φ z)` using `by filter_upwards [ae_all_iff.mpr (fun i => ae_coord_ne_zero (n := n) i)] with z hz`. Distinguish the cases in `hzv : z ∈ tsupport v`. Establish `huz : u z ≠ 0` using `hu0 z (hsub hzv)`. Establish `hp0 : ‖∏ i, z i ^ m i‖ ≠ 0`.

Rewrite using `[norm_ne_zero_iff]`. Conclude with `Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero _ (hz i))`. Rewrite using `[norm_mul, Real.log_mul (norm_ne_zero_iff.mpr huz) hp0, log_norm_prod_zpow_eq_logMono m z hz, logMono, add_mul, Finset.sum_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `h0 : densV v φ z = 0` using `maDens_cons_eq_zero φ hzv`. Simplify using `[h0]`. Use `⟨(hIu.add hIs).congr hae.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_congr_ae hae, integral_add hIu hIs, hEu, zero_add, integral_finset_sum Finset.univ (fun i _ => (hI i).const_mul (m i : ℝ))]`.

Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Use `first`. Consider the case `rw [integral_const_mul]`. Consider the case `rw [integral_mul_left]`. Rewrite using `[hE i]`.
-/
theorem log_norm_integral_formula_snc : PoincareLelongNormalCrossing := by
  intro n m U v φ u hp hu hu0
  obtain ⟨-, -, -, hsub, -⟩ := id hp
  have hI : ∀ i, Integrable (fun z : Fin (n + 1) → ℂ => Real.log ‖z i‖ * densV v φ z) volume :=
    fun i => (log_norm_integral_at_coordinate n i U v φ hp).1
  have hE : ∀ i, ∫ z, Real.log ‖z i‖ * densV v φ z = ∫ w, v (hypInclAt i w) * densHypAt i φ w :=
    fun i => (log_norm_integral_at_coordinate n i U v φ hp).2.2
  obtain ⟨hIu, hEu⟩ := unit_part hp hu hu0
  have hIs : Integrable (fun z : Fin (n + 1) → ℂ =>
      ∑ i ∈ Finset.univ, (m i : ℝ) * (Real.log ‖z i‖ * densV v φ z)) volume :=
    integrable_finset_sum Finset.univ (fun i _ => (hI i).const_mul (m i : ℝ))
  have hae : (fun z : Fin (n + 1) → ℂ => Real.log ‖u z * ∏ i, z i ^ m i‖ * densV v φ z) =ᵐ[volume]
      fun z => Real.log ‖u z‖ * densV v φ z +
        ∑ i ∈ Finset.univ, (m i : ℝ) * (Real.log ‖z i‖ * densV v φ z) := by
    filter_upwards [ae_all_iff.mpr (fun i => ae_coord_ne_zero (n := n) i)] with z hz
    by_cases hzv : z ∈ tsupport v
    · have huz : u z ≠ 0 := hu0 z (hsub hzv)
      have hp0 : ‖∏ i, z i ^ m i‖ ≠ 0 := by
        rw [norm_ne_zero_iff]
        exact Finset.prod_ne_zero_iff.mpr (fun i _ => zpow_ne_zero _ (hz i))
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr huz) hp0,
        log_norm_prod_zpow_eq_logMono m z hz, logMono, add_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    · have h0 : densV v φ z = 0 := maDens_cons_eq_zero φ hzv
      simp [h0]
  refine ⟨(hIu.add hIs).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_add hIu hIs, hEu, zero_add,
    integral_finset_sum Finset.univ (fun i _ => (hI i).const_mul (m i : ℝ))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  first
    | rw [integral_const_mul]
    | rw [integral_mul_left]
  rw [hE i]

end ReciprocityTheory.AnForm.A
