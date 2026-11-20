import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ComplexDoubleCosets.CplxDC
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldDCUnfold

open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

namespace PI.PoincareSeriesInner.W

universe u

def cf : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]

def part (k : Fin 4) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (![z.re, -z.re, z.im, -z.im] k)

/- English proof (translation)
The claim follows from `ENNReal.ofReal_ne_top`.
-/
theorem part_ne_top (k : Fin 4) (z : ℂ) : part k z ≠ ⊤ := ENNReal.ofReal_ne_top

/- English proof (translation)
Rewrite using `[← ofReal_norm_eq_enorm]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Use `fin_cases k`. Simplify using `using Complex.re_le_norm z`. Simplify using `using le_trans (neg_le_abs z.re) (Complex.abs_re_le_norm z)`.

Simplify using `using Complex.im_le_norm z`. Simplify using `using le_trans (neg_le_abs z.im) (Complex.abs_im_le_norm z)`.
-/
theorem part_le (k : Fin 4) (z : ℂ) : part k z ≤ ‖z‖ₑ := by
  rw [← ofReal_norm_eq_enorm]
  apply ENNReal.ofReal_le_ofReal
  fin_cases k
  · simpa using Complex.re_le_norm z
  · simpa using le_trans (neg_le_abs z.re) (Complex.abs_re_le_norm z)
  · simpa using Complex.im_le_norm z
  · simpa using le_trans (neg_le_abs z.im) (Complex.abs_im_le_norm z)

/- English proof (translation)
Use `fin_cases k`. Conclude with `ENNReal.measurable_ofReal.comp Complex.measurable_re`. Conclude with `ENNReal.measurable_ofReal.comp Complex.measurable_re.neg`. Conclude with `ENNReal.measurable_ofReal.comp Complex.measurable_im`. Conclude with `ENNReal.measurable_ofReal.comp Complex.measurable_im.neg`.
-/
theorem measurable_part (k : Fin 4) : Measurable (part k) := by
  fin_cases k
  · exact ENNReal.measurable_ofReal.comp Complex.measurable_re
  · exact ENNReal.measurable_ofReal.comp Complex.measurable_re.neg
  · exact ENNReal.measurable_ofReal.comp Complex.measurable_im
  · exact ENNReal.measurable_ofReal.comp Complex.measurable_im.neg

/- English proof (translation)
Simplify using `only [Fin.sum_univ_four, cf, part]`. Apply the tactic sequence `apply Complex.ext <;> simp [ENNReal.toReal_ofReal'] <;>`. Combine the linear relations using `[max_zero_sub_max_neg_zero_eq_self z.re, max_zero_sub_max_neg_zero_eq_self z.im]`.
-/
theorem split (z : ℂ) : z = ∑ k, cf k * ((part k z).toReal : ℂ) := by
  simp only [Fin.sum_univ_four, cf, part]
  apply Complex.ext <;> simp [ENNReal.toReal_ofReal'] <;>
    linarith [max_zero_sub_max_neg_zero_eq_self z.re, max_zero_sub_max_neg_zero_eq_self z.im]

/- English proof (translation)
Use `⟨(integrable_toReal_of_lintegral_ne_top hf hfin).ofReal, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_complex_ofReal, integral_toReal hf (Filter.Eventually.of_forall fun x => (hpt x).lt_top)]`.
-/
theorem toReal_int {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hfin : ∫⁻ x, f x ∂ν ≠ ⊤) (hpt : ∀ x, f x ≠ ⊤) :
    Integrable (fun x => ((f x).toReal : ℂ)) ν ∧
      ∫ x, ((f x).toReal : ℂ) ∂ν = (((∫⁻ x, f x ∂ν).toReal : ℝ) : ℂ) := by
  refine ⟨(integrable_toReal_of_lintegral_ne_top hf hfin).ofReal, ?_⟩
  rw [integral_complex_ofReal, integral_toReal hf (Filter.Eventually.of_forall fun x => (hpt x).lt_top)]

/- English proof (translation)
Establish `hsum : ∀ k, Summable (fun δ : E => ((v k ((δ : G) * x)).toReal : ℂ))` using `fun k => Complex.summable_ofReal.2 (ENNReal.summable_toReal (hv k x))`. Unfold `poinc`. Repeatedly rewrite using `[hf]`. Rewrite using `[Summable.tsum_finsetSum (fun k _ => (hsum k).mul_left (cf k))]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[tsum_mul_left, ← Complex.ofReal_tsum, ENNReal.tsum_toReal_eq (fun δ => ENNReal.ne_top_of_tsum_ne_top (hv k x) δ)]`.
-/
theorem poinc_split {G : Type*} [Group G] (E : Set G) (v : Fin 4 → G → ℝ≥0∞) (f : G → ℂ)
    (hf : ∀ x, f x = ∑ k, cf k * ((v k x).toReal : ℂ))
    (hv : ∀ k x, ∑' δ : E, v k ((δ : G) * x) ≠ ⊤) (x : G) :
    poinc E f x = ∑ k, cf k * (((∑' δ : E, v k ((δ : G) * x))).toReal : ℂ) := by
  have hsum : ∀ k, Summable (fun δ : E => ((v k ((δ : G) * x)).toReal : ℂ)) :=
    fun k => Complex.summable_ofReal.2 (ENNReal.summable_toReal (hv k x))
  unfold poinc
  simp_rw [hf]
  rw [Summable.tsum_finsetSum (fun k _ => (hsum k).mul_left (cf k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tsum_mul_left, ← Complex.ofReal_tsum, ENNReal.tsum_toReal_eq (fun δ => ENNReal.ne_top_of_tsum_ne_top (hv k x) δ)]

/- English proof (translation)
Rewrite using `[Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.toReal_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul (a b : Fin 4 → ℝ≥0∞) :
    (∑ k, cf k * ((a k).toReal : ℂ)) * (∑ j, cf j * ((b j).toReal : ℂ)) =
      ∑ k, ∑ j, cf k * cf j * (((a k * b j).toReal : ℝ) : ℂ) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.toReal_mul]; push_cast; ring

/- English proof (translation)
Unfold `CplxDC`. Introduce `G _ _ _ μ _ Γ S S' _ hSΓ hS'Γ D D' hD hD' R hR Fs hFs FΓ hFΓ φ ψ hφ hψ hφS hψS hφf hψf hfin`. Establish `hΓc : (Γ : Set G).Countable` using `Set.countable_coe_iff.1 (by assumption)`. Use `haveI : Countable D := (hΓc.mono hD.1).to_subtype`. Use `haveI : Countable D' := (hΓc.mono hD'.1).to_subtype`.

Use `set g : Fin 4 → G → ℝ≥0∞ := fun k y => part k (φ y) with hg_def`. Use `set h : Fin 4 → G → ℝ≥0∞ := fun j y => part j (ψ y) with hh_def`. Establish `hgm : ∀ k, Measurable (g k)` using `fun k => (measurable_part k).comp hφ`. Establish `hhm : ∀ j, Measurable (h j)` using `fun j => (measurable_part j).comp hψ`. Establish `hgS : ∀ k, ∀ s ∈ S, ∀ y, g k (s * y) = g k y` using `fun k s hs y => by simp only [g, hφS s hs y]`.

Establish `hhS : ∀ j, ∀ s ∈ S', ∀ y, h j (s * y) = h j y` using `fun j s hs y => by simp only [h, hψS s hs y]`. Establish `hA : ∀ k x, ∑' δ : D, g k ((δ : G) * x) ≤ ∑' δ : D, ‖φ ((δ : G) * x)‖ₑ` using `fun k x => ENNReal.tsum_le_tsum fun δ => part_le k _`. Establish `hB : ∀ j x, ∑' δ : D', h j ((δ : G) * x) ≤ ∑' δ : D', ‖ψ ((δ : G) * x)‖ₑ` using `fun j x => ENNReal.tsum_le_tsum fun δ => part_le j _`. Establish `hAfin : ∀ k x, ∑' δ : D, g k ((δ : G) * x) ≠ ⊤` using `fun k x => ne_top_of_le_ne_top (hφf x) (hA k x)`. Establish `hBfin : ∀ j x, ∑' δ : D', h j ((δ : G) * x) ≠ ⊤` using `fun j x => ne_top_of_le_ne_top (hψf x) (hB j x)`.

Establish `hprod : ∀ x, poinc D φ x * poinc D' ψ x = ∑ k, ∑ j, cf k * cf j * ((((∑' δ : D, g k ((δ : G) * x)) * ∑' δ : D', h j ((δ : G) * x)).toReal : ℝ) : ℂ)` using `fun x => by`. Rewrite using `[poinc_split D g φ (fun y => split (φ y)) hAfin x, poinc_split D' h ψ (fun y => split (ψ y)) hBfin x, sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul]`. Establish `hABm : ∀ k j, Measurable (fun x => (∑' δ : D, g k ((δ : G) * x)) * ∑' δ : D', h j ((δ : G) * x))` using `fun k j => (Measurable.ennreal_tsum fun δ => (hgm k).comp (measurable_const_mul _)).mul (Measurable.ennreal_tsum fun δ => (hhm j).comp (measurable_const_mul _))`. Establish `hABfin : ∀ k j, ∫⁻ x in FΓ, (∑' δ : D, g k ((δ : G) * x)) * ∑' δ : D', h j ((δ : G) * x) ∂μ ≠ ⊤` using `fun k j => ne_top_of_le_ne_top hfin (lintegral_mono fun x => mul_le_mul' (hA k x) (hB j x))`. Establish `hint` using `fun k j => toReal_int (ν := μ.restrict FΓ) (hABm k j).aemeasurable (hABfin k j) (fun x => ENNReal.mul_ne_top (hAfin k x) (hBfin j x))`.

Establish `hunf : ∀ k j, ∫⁻ x in FΓ, (∑' δ : D, g k ((δ : G) * x)) * ∑' δ : D', h j ((δ : G) * x) ∂μ = ∑' r : R, ∫⁻ x in Fs r, g k x * h j ((r : G)⁻¹ * x) ∂μ` using `fun k j => fold_dc_unfold G μ Γ S S' hSΓ hS'Γ D D' hD hD' R hR Fs hFs FΓ hFΓ (g k) (h j) (hgm k) (hhm j) (hgS k) (hhS j)`. Establish `hIfin : ∀ k j (r : R), ∫⁻ x in Fs r, g k x * h j ((r : G)⁻¹ * x) ∂μ ≠ ⊤` using `fun k j r => ENNReal.ne_top_of_tsum_ne_top (by rw [← hunf k j]; exact hABfin k j) r`. Establish `hrint` using `fun k j (r : R) => toReal_int (ν := μ.restrict (Fs r)) (f := fun x => g k x * h j ((r : G)⁻¹ * x)) ((hgm k).mul ((hhm j).comp (measurable_const_mul _))).aemeasurable (hIfin k j r) (fun x => ENNReal.mul_ne_top (part_ne_top _ _) (part_ne_top _ _))`. Establish `hprod2 : ∀ (r : G) x, φ x * ψ (r⁻¹ * x) = ∑ k, ∑ j, cf k * cf j * (((g k x * h j (r⁻¹ * x)).toReal : ℝ) : ℂ)` using `fun r x => by`. Rewrite using `[split (φ x), split (ψ (r⁻¹ * x))]`.

Conclude with `sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul _ _`. Establish `hsI : ∀ k j, Summable (fun r : R => (((∫⁻ x in Fs r, g k x * h j ((r : G)⁻¹ * x) ∂μ).toReal : ℝ) : ℂ))` using `fun k j => Complex.summable_ofReal.2 (ENNReal.summable_toReal (by rw [← hunf k j]; exact hABfin k j))`. Rewrite using `[show (fun x => poinc D φ x * poinc D' ψ x) = _ from funext hprod]`. Establish `hI1 : Integrable (fun x => ∑ k, ∑ j, cf k * cf j * ((((∑' δ : D, g k ((δ : G) * x)) * ∑' δ : D', h j ((δ : G) * x)).toReal : ℝ) : ℂ)) (μ.restrict FΓ)` using `integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun j _ => ((hint k j).1).const_mul _`. Use `⟨hI1, ?_⟩` and prove the remaining obligations.

Establish `hr : ∀ r : R, ∫ x in Fs r, φ x * ψ ((r : G)⁻¹ * x) ∂μ = ∑ k, ∑ j, cf k * cf j * (((∫⁻ x in Fs r, g k x * h j ((r : G)⁻¹ * x) ∂μ).toReal : ℝ) : ℂ)`. Introduce `r`. Repeatedly rewrite using `[hprod2 (r : G)]`. Rewrite using `[integral_finset_sum _ (fun k _ => integrable_finset_sum _ fun j _ => ((hrint k j r).1).const_mul _)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[integral_finset_sum _ (fun j _ => ((hrint k j r).1).const_mul _)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[integral_const_mul, (hrint k j r).2]`. Rewrite using `[tsum_congr hr, integral_finset_sum _ (fun k _ => integrable_finset_sum _ fun j _ => ((hint k j).1).const_mul _), Summable.tsum_finsetSum (fun k _ => summable_sum fun j _ => (hsI k j).mul_left _)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[integral_finset_sum _ (fun j _ => ((hint k j).1).const_mul _), Summable.tsum_finsetSum (fun j _ => (hsI k j).mul_left _)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[integral_const_mul, (hint k j).2, hunf k j, tsum_mul_left, ← Complex.ofReal_tsum, ENNReal.tsum_toReal_eq (hIfin k j)]`.
-/
theorem complex_double_coset : CplxDC.{u} := by
  unfold CplxDC
  intro G _ _ _ μ _ Γ S S' _ hSΓ hS'Γ D D' hD hD' R hR Fs hFs FΓ hFΓ φ ψ hφ hψ hφS hψS hφf hψf hfin
  have hΓc : (Γ : Set G).Countable := Set.countable_coe_iff.1 (by assumption)
  haveI : Countable D := (hΓc.mono hD.1).to_subtype
  haveI : Countable D' := (hΓc.mono hD'.1).to_subtype
  set g : Fin 4 → G → ℝ≥0∞ := fun k y => part k (φ y) with hg_def
  set h : Fin 4 → G → ℝ≥0∞ := fun j y => part j (ψ y) with hh_def
  have hgm : ∀ k, Measurable (g k) := fun k => (measurable_part k).comp hφ
  have hhm : ∀ j, Measurable (h j) := fun j => (measurable_part j).comp hψ
  have hgS : ∀ k, ∀ s ∈ S, ∀ y, g k (s * y) = g k y := fun k s hs y => by simp only [g, hφS s hs y]
  have hhS : ∀ j, ∀ s ∈ S', ∀ y, h j (s * y) = h j y := fun j s hs y => by simp only [h, hψS s hs y]
  have hA : ∀ k x, ∑' δ : D, g k ((δ : G) * x) ≤ ∑' δ : D, ‖φ ((δ : G) * x)‖ₑ :=
    fun k x => ENNReal.tsum_le_tsum fun δ => part_le k _
  have hB : ∀ j x, ∑' δ : D', h j ((δ : G) * x) ≤ ∑' δ : D', ‖ψ ((δ : G) * x)‖ₑ :=
    fun j x => ENNReal.tsum_le_tsum fun δ => part_le j _
  have hAfin : ∀ k x, ∑' δ : D, g k ((δ : G) * x) ≠ ⊤ := fun k x => ne_top_of_le_ne_top (hφf x) (hA k x)
  have hBfin : ∀ j x, ∑' δ : D', h j ((δ : G) * x) ≠ ⊤ := fun j x => ne_top_of_le_ne_top (hψf x) (hB j x)
  have hprod : ∀ x, poinc D φ x * poinc D' ψ x = ∑ k, ∑ j, cf k * cf j *
      ((((∑' δ : D, g k ((δ : G) * x)) * ∑' δ : D', h j ((δ : G) * x)).toReal : ℝ) : ℂ) := fun x => by
    rw [poinc_split D g φ (fun y => split (φ y)) hAfin x, poinc_split D' h ψ (fun y => split (ψ y)) hBfin x,
      sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul]
  have hABm : ∀ k j, Measurable (fun x => (∑' δ : D, g k ((δ : G) * x)) * ∑' δ : D', h j ((δ : G) * x)) :=
    fun k j => (Measurable.ennreal_tsum fun δ => (hgm k).comp (measurable_const_mul _)).mul
      (Measurable.ennreal_tsum fun δ => (hhm j).comp (measurable_const_mul _))
  have hABfin : ∀ k j, ∫⁻ x in FΓ, (∑' δ : D, g k ((δ : G) * x)) * ∑' δ : D', h j ((δ : G) * x) ∂μ ≠ ⊤ :=
    fun k j => ne_top_of_le_ne_top hfin (lintegral_mono fun x => mul_le_mul' (hA k x) (hB j x))
  have hint := fun k j => toReal_int (ν := μ.restrict FΓ) (hABm k j).aemeasurable (hABfin k j)
    (fun x => ENNReal.mul_ne_top (hAfin k x) (hBfin j x))
  have hunf : ∀ k j, ∫⁻ x in FΓ, (∑' δ : D, g k ((δ : G) * x)) * ∑' δ : D', h j ((δ : G) * x) ∂μ =
      ∑' r : R, ∫⁻ x in Fs r, g k x * h j ((r : G)⁻¹ * x) ∂μ := fun k j =>
    fold_dc_unfold G μ Γ S S' hSΓ hS'Γ D D' hD hD' R hR Fs hFs FΓ hFΓ (g k) (h j) (hgm k) (hhm j)
      (hgS k) (hhS j)
  have hIfin : ∀ k j (r : R), ∫⁻ x in Fs r, g k x * h j ((r : G)⁻¹ * x) ∂μ ≠ ⊤ := fun k j r =>
    ENNReal.ne_top_of_tsum_ne_top (by rw [← hunf k j]; exact hABfin k j) r
  have hrint := fun k j (r : R) => toReal_int (ν := μ.restrict (Fs r)) (f := fun x => g k x * h j ((r : G)⁻¹ * x))
    ((hgm k).mul ((hhm j).comp (measurable_const_mul _))).aemeasurable (hIfin k j r)
    (fun x => ENNReal.mul_ne_top (part_ne_top _ _) (part_ne_top _ _))
  have hprod2 : ∀ (r : G) x, φ x * ψ (r⁻¹ * x) =
      ∑ k, ∑ j, cf k * cf j * (((g k x * h j (r⁻¹ * x)).toReal : ℝ) : ℂ) := fun r x => by
    rw [split (φ x), split (ψ (r⁻¹ * x))]
    exact sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul _ _
  have hsI : ∀ k j, Summable (fun r : R => (((∫⁻ x in Fs r, g k x * h j ((r : G)⁻¹ * x) ∂μ).toReal : ℝ) : ℂ)) :=
    fun k j => Complex.summable_ofReal.2 (ENNReal.summable_toReal (by rw [← hunf k j]; exact hABfin k j))
  rw [show (fun x => poinc D φ x * poinc D' ψ x) = _ from funext hprod]
  have hI1 : Integrable (fun x => ∑ k, ∑ j, cf k * cf j *
      ((((∑' δ : D, g k ((δ : G) * x)) * ∑' δ : D', h j ((δ : G) * x)).toReal : ℝ) : ℂ)) (μ.restrict FΓ) :=
    integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun j _ => ((hint k j).1).const_mul _
  refine ⟨hI1, ?_⟩
  have hr : ∀ r : R, ∫ x in Fs r, φ x * ψ ((r : G)⁻¹ * x) ∂μ =
      ∑ k, ∑ j, cf k * cf j * (((∫⁻ x in Fs r, g k x * h j ((r : G)⁻¹ * x) ∂μ).toReal : ℝ) : ℂ) := by
    intro r
    simp_rw [hprod2 (r : G)]
    rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _ fun j _ => ((hrint k j r).1).const_mul _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finset_sum _ (fun j _ => ((hrint k j r).1).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, (hrint k j r).2]
  rw [tsum_congr hr, integral_finset_sum _ (fun k _ => integrable_finset_sum _ fun j _ => ((hint k j).1).const_mul _),
    Summable.tsum_finsetSum (fun k _ => summable_sum fun j _ => (hsI k j).mul_left _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finset_sum _ (fun j _ => ((hint k j).1).const_mul _),
    Summable.tsum_finsetSum (fun j _ => (hsI k j).mul_left _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, (hint k j).2, hunf k j, tsum_mul_left, ← Complex.ofReal_tsum,
    ENNReal.tsum_toReal_eq (hIfin k j)]

end PI.PoincareSeriesInner.W
