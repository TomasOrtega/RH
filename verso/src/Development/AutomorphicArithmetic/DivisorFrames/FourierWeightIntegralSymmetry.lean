import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
open MeasureTheory FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

namespace FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB.Tate

variable {ι : Type} [Fintype ι]

/- English proof (translation)
Establish `h0 : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0` using `compl_mem_ae_iff.2 (measure_singleton 0)`. Conclude with `ae_all_iff.2 fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => (volume : Measure ℂ)) (i := i)).eventually h0`.
-/
private theorem ae_ne : ∀ᵐ b ∂(volume : Measure (ι → ℂ)), ∀ i, b i ≠ 0 := by
  have h0 : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  exact ae_all_iff.2 fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => (volume : Measure ℂ)) (i := i)).eventually h0

/- English proof (translation)
Set `L : (ι → ℂ) →ₗ[ℝ] (ι → ℂ)` to `LinearMap.pi fun i => (Algebra.lmul ℝ ℂ (s i)).comp (LinearMap.proj i)`. Establish `hdet : LinearMap.det L = nm s`. Rewrite using `[LinearMap.det_pi, nm]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]`.

Establish `hL : (fun y => s * y) = L`. Use function extensionality and compare the values at `y i`. Simplify using `[L]`. Rewrite using `[hL, Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact (nm_pos hs).ne'), hdet, abs_of_pos (inv_pos.2 (nm_pos hs))]`.
-/
private theorem map_mul_vol {s : ι → ℂ} (hs : ∀ w, s w ≠ 0) :
    (volume : Measure (ι → ℂ)).map (fun y => s * y) = ENNReal.ofReal (nm s)⁻¹ • volume := by
  let L : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) :=
    LinearMap.pi fun i => (Algebra.lmul ℝ ℂ (s i)).comp (LinearMap.proj i)
  have hdet : LinearMap.det L = nm s := by
    rw [LinearMap.det_pi, nm]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have hL : (fun y => s * y) = L := by
    funext y i
    simp [L]
  rw [hL, Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact (nm_pos hs).ne'), hdet,
    abs_of_pos (inv_pos.2 (nm_pos hs))]

/- English proof (translation)
Establish `hm : Measurable fun y : ι → ℂ => s * y` using `measurable_const_mul s`. Establish `hG' : Integrable G ((volume : Measure (ι → ℂ)).map (fun y => s * y))`. Rewrite using `[map_mul_vol hs]`. Conclude with `hG.smul_measure ENNReal.ofReal_ne_top`. Rewrite using `[← integral_map hm.aemeasurable hG'.1, map_mul_vol hs, integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 (nm_pos hs)).le]`.
-/
private theorem integral_scale {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : ι → ℂ} (hs : ∀ w, s w ≠ 0)
    {G : (ι → ℂ) → E} (hG : Integrable G) : ∫ y, G (s * y) = (nm s)⁻¹ • ∫ y, G y := by
  have hm : Measurable fun y : ι → ℂ => s * y := measurable_const_mul s
  have hG' : Integrable G ((volume : Measure (ι → ℂ)).map (fun y => s * y)) := by
    rw [map_mul_vol hs]; exact hG.smul_measure ENNReal.ofReal_ne_top
  rw [← integral_map hm.aemeasurable hG'.1, map_mul_vol hs, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_pos.2 (nm_pos hs)).le]

/- English proof (translation)
Establish `hm : Measurable fun y : ι → ℂ => s * y` using `measurable_const_mul s`. Establish `hG' : Integrable G ((volume : Measure (ι → ℂ)).map (fun y => s * y))`. Rewrite using `[map_mul_vol hs]`. Conclude with `hG.smul_measure ENNReal.ofReal_ne_top`. Conclude with `hG'.comp_measurable hm`.
-/
private theorem integrable_scale {s : ι → ℂ} (hs : ∀ w, s w ≠ 0)
    {G : (ι → ℂ) → ℂ} (hG : Integrable G) : Integrable fun y => G (s * y) := by
  have hm : Measurable fun y : ι → ℂ => s * y := measurable_const_mul s
  have hG' : Integrable G ((volume : Measure (ι → ℂ)).map (fun y => s * y)) := by
    rw [map_mul_vol hs]; exact hG.smul_measure ENNReal.ofReal_ne_top
  exact hG'.comp_measurable hm

/- English proof (translation)
Use `continuous_of_dominated (bound := fun s => ‖h s‖) (fun y => ?_) (fun y => ?_) hh.norm ?_` and prove the remaining obligations. Conclude with `hh.1.mul (continuous_ec.comp (by fun_prop)).aestronglyMeasurable`. Conclude with `Filter.Eventually.of_forall fun s => by rw [norm_mul, norm_ec, mul_one]`. Conclude with `Filter.Eventually.of_forall fun s => continuous_const.mul (continuous_ec.comp (by fun_prop))`.
-/
private theorem continuous_FT {h : (ι → ℂ) → ℂ} (hh : Integrable h) : Continuous (FT h) := by
  refine continuous_of_dominated (bound := fun s => ‖h s‖) (fun y => ?_) (fun y => ?_) hh.norm ?_
  · exact hh.1.mul (continuous_ec.comp (by fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun s => by rw [norm_mul, norm_ec, mul_one]
  · exact Filter.Eventually.of_forall fun s => continuous_const.mul (continuous_ec.comp (by fun_prop))

/- English proof (translation)
Establish `key : ∀ s : ι → ℂ, (∀ w, s w ≠ 0) → ∀ y, a s * F (s * y) * dwt κ e y = (a s * wt κ e s * (nm s : ℂ)) * (F (s * y) * dwt κ e (s * y))`. Introduce `s hs y`. Establish `h1` using `wt_ne_zero κ e hs`. Establish `h2 : (nm s : ℂ) ≠ 0` using `by exact_mod_cast (nm_pos hs).ne'`. Rewrite using `[dwt_mul, show dwt κ e s = (wt κ e s * (nm s : ℂ))⁻¹ from rfl]`.

Clear the denominators using the available nonvanishing facts. Establish `hm : AEStronglyMeasurable (Function.uncurry fun s y => a s * F (s * y) * dwt κ e y) ((volume : Measure (ι → ℂ)).prod (volume : Measure (ι → ℂ)))` using `(ha.1.comp_fst.mul (hF.comp continuous_mul).aestronglyMeasurable).mul ((measurable_dwt κ e).comp measurable_snd).aestronglyMeasurable`. Establish `hI : Integrable (Function.uncurry fun s y => a s * F (s * y) * dwt κ e y) ((volume : Measure (ι → ℂ)).prod (volume : Measure (ι → ℂ)))`. Use `(integrable_prod_iff hm).2 ⟨?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [ae_ne] with s hs`.

Simplify using `only [Function.uncurry_apply_pair, key s hs]`. Conclude with `(integrable_scale hs hG).const_mul _`. Use `(haw.norm.mul_const (∫ y, ‖F y * dwt κ e y‖)).congr ?_ filter_upwards [ae_ne] with s hs` and prove the remaining obligations. Simplify using `only [Function.uncurry_apply_pair, key s hs]`. Establish `hp` using `nm_pos hs`.

Repeatedly rewrite using `[norm_mul (a s * wt κ e s * (nm s : ℂ))]`. Rewrite using `[integral_const_mul, integral_scale hs hG.norm, norm_mul (a s * wt κ e s), Complex.norm_real, Real.norm_of_nonneg hp.le, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Repeatedly rewrite using `[← integral_mul_const (dwt κ e _)]`. Rewrite using `[← integral_integral_swap hI, ← integral_mul_const]`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_ne] with s hs`. Establish `h2 : (nm s : ℂ) ≠ 0` using `by exact_mod_cast (nm_pos hs).ne'`. Simplify using `only [key s hs]`. Rewrite using `[integral_const_mul, integral_scale hs hG, Complex.real_smul, Complex.ofReal_inv]`.

Clear the denominators using the available nonvanishing facts.
-/
private theorem unfold_weight (κ : ι → ℤ) (e : ℕ) {a F : (ι → ℂ) → ℂ} (ha : Integrable a) (hF : Continuous F)
    (haw : Integrable fun s => a s * wt κ e s) (hG : Integrable fun y => F y * dwt κ e y) :
    (∫ s, a s * wt κ e s) * (∫ y, F y * dwt κ e y) = ∫ y, (∫ s, a s * F (s * y)) * dwt κ e y := by
  have key : ∀ s : ι → ℂ, (∀ w, s w ≠ 0) → ∀ y, a s * F (s * y) * dwt κ e y =
      (a s * wt κ e s * (nm s : ℂ)) * (F (s * y) * dwt κ e (s * y)) := by
    intro s hs y
    have h1 := wt_ne_zero κ e hs
    have h2 : (nm s : ℂ) ≠ 0 := by exact_mod_cast (nm_pos hs).ne'
    rw [dwt_mul, show dwt κ e s = (wt κ e s * (nm s : ℂ))⁻¹ from rfl]
    field_simp
  have hm : AEStronglyMeasurable (Function.uncurry fun s y => a s * F (s * y) * dwt κ e y)
      ((volume : Measure (ι → ℂ)).prod (volume : Measure (ι → ℂ))) :=
    (ha.1.comp_fst.mul (hF.comp continuous_mul).aestronglyMeasurable).mul
      ((measurable_dwt κ e).comp measurable_snd).aestronglyMeasurable
  have hI : Integrable (Function.uncurry fun s y => a s * F (s * y) * dwt κ e y)
      ((volume : Measure (ι → ℂ)).prod (volume : Measure (ι → ℂ))) := by
    refine (integrable_prod_iff hm).2 ⟨?_, ?_⟩
    · filter_upwards [ae_ne] with s hs
      simp only [Function.uncurry_apply_pair, key s hs]
      exact (integrable_scale hs hG).const_mul _
    · refine (haw.norm.mul_const (∫ y, ‖F y * dwt κ e y‖)).congr ?_
      filter_upwards [ae_ne] with s hs
      simp only [Function.uncurry_apply_pair, key s hs]
      have hp := nm_pos hs
      simp_rw [norm_mul (a s * wt κ e s * (nm s : ℂ))]
      rw [integral_const_mul, integral_scale hs hG.norm, norm_mul (a s * wt κ e s), Complex.norm_real,
        Real.norm_of_nonneg hp.le, smul_eq_mul]
      field_simp
  simp_rw [← integral_mul_const (dwt κ e _)]
  rw [← integral_integral_swap hI, ← integral_mul_const]
  refine integral_congr_ae ?_
  filter_upwards [ae_ne] with s hs
  have h2 : (nm s : ℂ) ≠ 0 := by exact_mod_cast (nm_pos hs).ne'
  simp only [key s hs]
  rw [integral_const_mul, integral_scale hs hG, Complex.real_smul, Complex.ofReal_inv]
  field_simp

/- English proof (translation)
Establish `hI : Integrable (Function.uncurry fun s u => a s * h u * ec (u * (s * y))) ((volume : Measure (ι → ℂ)).prod (volume : Measure (ι → ℂ)))` using `(ha.mul_prod hh).mul_bdd (c := 1) (continuous_ec.comp (f := fun p : (ι → ℂ) × (ι → ℂ) => p.2 * (p.1 * y)) (by fun_prop)).aestronglyMeasurable (Filter.Eventually.of_forall fun p => (norm_ec _).le)`. Simplify using `only [FT, ← integral_const_mul, ← mul_assoc (a _)]`. Rewrite using `[integral_integral_swap hI]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Use `integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[mul_left_comm u s y]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem symm_FT {a h : (ι → ℂ) → ℂ} (ha : Integrable a) (hh : Integrable h) (y : ι → ℂ) :
    ∫ s, a s * FT h (s * y) = ∫ s, h s * FT a (s * y) := by
  have hI : Integrable (Function.uncurry fun s u => a s * h u * ec (u * (s * y)))
      ((volume : Measure (ι → ℂ)).prod (volume : Measure (ι → ℂ))) :=
    (ha.mul_prod hh).mul_bdd (c := 1)
      (continuous_ec.comp (f := fun p : (ι → ℂ) × (ι → ℂ) => p.2 * (p.1 * y)) (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => (norm_ec _).le)
  simp only [FT, ← integral_const_mul, ← mul_assoc (a _)]
  rw [integral_integral_swap hI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  beta_reduce
  rw [mul_left_comm u s y]
  ring

end FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB.Tate

open FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB.Tate in
/- English proof (translation)
Introduce `ι _ κ e a h ha hh haw hhw hFa hFh`. Rewrite using `[unfold_weight κ e ha (continuous_FT hh) haw hFh, unfold_weight κ e hh (continuous_FT ha) hhw hFa]`. Simplify using `only [symm_FT ha hh]`.
-/
theorem UpperTheory.fourier_weight_integral_symmetry :
    ∀ {ι : Type} [Fintype ι] (κ : ι → ℤ) (e : ℕ) (a h : (ι → ℂ) → ℂ), Integrable a → Integrable h →
        Integrable (fun s => a s * wt κ e s) → Integrable (fun s => h s * wt κ e s) →
        Integrable (fun y => FT a y * dwt κ e y) → Integrable (fun y => FT h y * dwt κ e y) →
        (∫ s, a s * wt κ e s) * (∫ y, FT h y * dwt κ e y) = (∫ s, h s * wt κ e s) * ∫ y, FT a y * dwt κ e y := by
  intro ι _ κ e a h ha hh haw hhw hFa hFh
  rw [unfold_weight κ e ha (continuous_FT hh) haw hFh, unfold_weight κ e hh (continuous_FT ha) hhw hFa]
  simp only [symm_FT ha hh]
