import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableRealWhittakerInverse
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableUnipotentFourierIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsIntegralTranslatesBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveIntegralBoundOfParts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePhi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoByTwoMajorantIntegrable
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultIntegralPowerBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightedDoubleIntegralBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableRadialCutoffWeightStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodIntegrandMajorantStatement

noncomputable section

open MeasureTheory
open Ad3 Ad3.LR Ad3.LR.C Ad3.LR.B

namespace GlobalTheory.CompanionTheory.PerUInt

def rtEquiv (g : GL (Fin 3) ℝ) : M23 ≃L[ℝ] M23 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun X => Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℝ))
      invFun := fun X => Matrix.of.symm (Matrix.of X * ((g⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ))
      map_add' := fun X Y => by
        show Matrix.of.symm ((Matrix.of X + Matrix.of Y) * (g : Matrix (Fin 3) (Fin 3) ℝ)) = _
        rw [Matrix.add_mul]
        rfl
      map_smul' := fun c X => by
        show Matrix.of.symm ((c • Matrix.of X) * (g : Matrix (Fin 3) (Fin 3) ℝ)) = _
        rw [Matrix.smul_mul]
        rfl
      left_inv := fun X => by
        simp [Matrix.mul_assoc]
      right_inv := fun X => by
        simp [Matrix.mul_assoc] }

def rtS (g : GL (Fin 3) ℝ) (Φ : Sw) : Sw :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rtEquiv g) Φ

/- English proof (translation)
Use function extensionality and compare the values at `X`. Simplify using `[rtS, B.rt, rtEquiv]`.
-/
theorem rtS_apply (g : GL (Fin 3) ℝ) (Φ : Sw) : ⇑(rtS g Φ) = B.rt g ⇑Φ := by
  funext X
  simp [rtS, B.rt, rtEquiv]

/- English proof (translation)
Establish `hv : Continuous (fun p : (ℝˣ × M22) × (Fin 2 → ℝ) => psiR (-(((p.1.1 : ℝ))⁻¹ * p.2 1)))`. Unfold `psiR`. Establish `: Continuous (fun p : (ℝˣ × M22) × (Fin 2 → ℝ) => ((p.1.1⁻¹ : ℝˣ) : ℝ))` using `Units.continuous_val.comp (continuous_inv.comp (continuous_fst.comp continuous_fst))`. Establish `h2 : (fun p : (ℝˣ × M22) × (Fin 2 → ℝ) => ((p.1.1 : ℝ))⁻¹) = fun p => ((p.1.1⁻¹ : ℝˣ) : ℝ)`. Use function extensionality and compare the values at `p`.

Simplify using the standard rewrite rules. Rewrite using `[show (fun p : (ℝˣ × M22) × (Fin 2 → ℝ) => Complex.exp (-2 * Real.pi * Complex.I * ((-(((p.1.1 : ℝ))⁻¹ * p.2 1) : ℝ) : ℂ))) = fun p => Complex.exp (-2 * Real.pi * Complex.I * ((-(((p.1.1⁻¹ : ℝˣ) : ℝ) * p.2 1) : ℝ) : ℂ)) by funext p; simp]`. Use `fun_prop`. Establish `hm : Continuous (fun p : (ℝˣ × M22) × (Fin 2 → ℝ) => Ψ (Matrix.of.symm (Matrix.of p.1.2 * blk p.2)))` using `hΨ.comp (GlobalTheory.CompanionTheory.GodementInt.continuous_mul_blk.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))`. Conclude with `((hm.mul hv).stronglyMeasurable.integral_prod_right' (ν := volume)).measurable`.
-/
theorem measurable_innB (Ψ : M23 → ℂ) (hΨ : Continuous Ψ) :
    Measurable (fun p : ℝˣ × M22 => innB Ψ p.2 (p.1 : ℝ)⁻¹) := by
  have hv : Continuous (fun p : (ℝˣ × M22) × (Fin 2 → ℝ) => psiR (-(((p.1.1 : ℝ))⁻¹ * p.2 1))) := by
    unfold psiR
    have : Continuous (fun p : (ℝˣ × M22) × (Fin 2 → ℝ) => ((p.1.1⁻¹ : ℝˣ) : ℝ)) :=
      Units.continuous_val.comp (continuous_inv.comp (continuous_fst.comp continuous_fst))
    have h2 : (fun p : (ℝˣ × M22) × (Fin 2 → ℝ) => ((p.1.1 : ℝ))⁻¹) = fun p => ((p.1.1⁻¹ : ℝˣ) : ℝ) := by
      funext p; simp
    rw [show (fun p : (ℝˣ × M22) × (Fin 2 → ℝ) => Complex.exp (-2 * Real.pi * Complex.I * ((-(((p.1.1 : ℝ))⁻¹ * p.2 1) : ℝ) : ℂ)))
      = fun p => Complex.exp (-2 * Real.pi * Complex.I * ((-(((p.1.1⁻¹ : ℝˣ) : ℝ) * p.2 1) : ℝ) : ℂ)) by funext p; simp]
    fun_prop
  have hm : Continuous (fun p : (ℝˣ × M22) × (Fin 2 → ℝ) =>
      Ψ (Matrix.of.symm (Matrix.of p.1.2 * blk p.2))) :=
    hΨ.comp (GlobalTheory.CompanionTheory.GodementInt.continuous_mul_blk.comp
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  exact ((hm.mul hv).stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

def domF (σ : ℝ) (g : ℝ → ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  g ((z.1.1 * z.2.2 - z.2.1 * z.1.2) / (z.1.1 ^ 2 + z.1.2 ^ 2)) * (z.1.1 ^ 2 + z.1.2 ^ 2) ^ (-1 - σ / 2) *
    (phi z.1.1 * phi z.1.2 * (phi z.2.1 * phi z.2.2))

/- English proof (translation)
Unfold `domF`. Use `((hgm.comp ?_).mul ?_).mul ?_` and prove the remaining obligations. Use `fun_prop`. Use `fun_prop`. Use `measurable_phi fun_prop` as an intermediate fact.
-/
theorem measurable_domF (σ : ℝ) (g : ℝ → ℝ) (hgm : Measurable g) : Measurable (domF σ g) := by
  unfold domF
  refine ((hgm.comp ?_).mul ?_).mul ?_
  · fun_prop
  · fun_prop
  · have := measurable_phi
    fun_prop

/- English proof (translation)
The claim follows from `mul_nonneg (mul_nonneg (hg0 _) (Real.rpow_nonneg (by positivity) _)) (mul_nonneg (mul_nonneg (phi_nonneg _) (phi_nonneg _)) (mul_nonneg (phi_nonneg _) (phi_nonneg _)))`.
-/
theorem domF_nonneg (σ : ℝ) (g : ℝ → ℝ) (hg0 : ∀ x, 0 ≤ g x) (z) : 0 ≤ domF σ g z :=
  mul_nonneg (mul_nonneg (hg0 _) (Real.rpow_nonneg (by positivity) _))
    (mul_nonneg (mul_nonneg (phi_nonneg _) (phi_nonneg _)) (mul_nonneg (phi_nonneg _) (phi_nonneg _)))

/- English proof (translation)
Establish `h0 : ∀ᵐ x : ℝ, x ≠ 0` using `compl_mem_ae_iff.2 (measure_singleton 0)`. Establish `h1 : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0` using `Measure.quasiMeasurePreserving_fst.ae h0`. Establish `h2 : ∀ᵐ p : ℝ × ℝ, p.2 ≠ 0` using `Measure.quasiMeasurePreserving_snd.ae h0`. Use `filter_upwards [h1, h2] with p a b using ⟨a, b⟩`.
-/
theorem ae_ne_zero : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 ∧ p.2 ≠ 0 := by
  have h0 : ∀ᵐ x : ℝ, x ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have h1 : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 := Measure.quasiMeasurePreserving_fst.ae h0
  have h2 : ∀ᵐ p : ℝ × ℝ, p.2 ≠ 0 := Measure.quasiMeasurePreserving_snd.ae h0
  filter_upwards [h1, h2] with p a b using ⟨a, b⟩

/- English proof (translation)
Establish `e : (w.1 * v.2 - v.1 * w.2) / (w.1 ^ 2 + w.2 ^ 2) = (w.1 / (w.1 ^ 2 + w.2 ^ 2)) * v.2 - (w.2 / (w.1 ^ 2 + w.2 ^ 2)) * v.1`. Clear the denominators using the available nonvanishing facts. Simplify using `only [domF, e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem domF_slice (σ : ℝ) (g : ℝ → ℝ) (w : ℝ × ℝ) (hw : w.1 ^ 2 + w.2 ^ 2 ≠ 0) (v : ℝ × ℝ) :
    domF σ g (w, v) = ((w.1 ^ 2 + w.2 ^ 2) ^ (-1 - σ / 2) * (phi w.1 * phi w.2)) *
      (g ((w.1 / (w.1 ^ 2 + w.2 ^ 2)) * v.2 - (w.2 / (w.1 ^ 2 + w.2 ^ 2)) * v.1) * (phi v.1 * phi v.2)) := by
  have e : (w.1 * v.2 - v.1 * w.2) / (w.1 ^ 2 + w.2 ^ 2) =
      (w.1 / (w.1 ^ 2 + w.2 ^ 2)) * v.2 - (w.2 / (w.1 ^ 2 + w.2 ^ 2)) * v.1 := by
    field_simp
  simp only [domF, e]
  ring

/- English proof (translation)
Establish `hsh` using `GlobalTheory.T.weighted_double_integral_bound g phi hgm measurable_phi hg integrable_phi hg0 phi_nonneg phi_le_one`. Establish `hout` using `GlobalTheory.T.integrable_radial_cutoff_weight σ h0 h1`. Establish `hm` using `measurable_domF σ g hgm`. Establish `hc2 : ∀ w : ℝ × ℝ, w.1 ≠ 0 → 0 < w.1 ^ 2 + w.2 ^ 2` using `fun w hw => by positivity`. Establish `hαβ : ∀ w : ℝ × ℝ, w.1 ≠ 0 → w.2 ≠ 0 → w.1 / (w.1 ^ 2 + w.2 ^ 2) ≠ 0 ∧ w.2 / (w.1 ^ 2 + w.2 ^ 2) ≠ 0` using `fun w a b => ⟨div_ne_zero a (hc2 w a).ne', div_ne_zero b (hc2 w a).ne'⟩`.

Rewrite using `[Measure.volume_eq_prod, integrable_prod_iff hm.aestronglyMeasurable]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [ae_ne_zero] with w hw`. Take `⟨a, b⟩` from `hw`. Take `⟨i1, -⟩` from `hsh _ _ (hαβ w a b).1 (hαβ w a b).2`.

Use `i1.const_mul ((w.1 ^ 2 + w.2 ^ 2) ^ (-1 - σ / 2) * (phi w.1 * phi w.2))` as an intermediate fact. Use `this.congr (ae_of_all _ fun v => ?_)` and prove the remaining obligations. Conclude with `(domF_slice σ g w (hc2 w a).ne' v).symm`. Use `Integrable.mono' (hout.const_mul ((∫ x, g x) * (∫ x, phi x))) ?_ ?_` and prove the remaining obligations. Conclude with `(hm.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable`.

Use `filter_upwards [ae_ne_zero] with w hw`. Take `⟨a, b⟩` from `hw`. Rewrite using `[Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]`. Establish `hc` using `hc2 w a`. Use `set c := w.1 ^ 2 + w.2 ^ 2 with hcdef`.

Take `⟨-, i2⟩` from `hsh _ _ (hαβ w a b).1 (hαβ w a b).2`. Establish `hmax : max |w.1 / c| |w.2 / c| = max |w.1| |w.2| / c`. Rewrite using `[abs_div, abs_div, abs_of_pos hc, max_div_div_right hc.le]`. Establish `hmpos : 0 < max |w.1| |w.2|` using `lt_max_of_lt_left (abs_pos.2 a)`. Establish `hP : 0 ≤ c ^ (-1 - σ / 2) * (phi w.1 * phi w.2)` using `mul_nonneg (Real.rpow_nonneg hc.le _) (mul_nonneg (phi_nonneg _) (phi_nonneg _))`.

Establish `hfn : ∀ v : ℝ × ℝ, ‖domF σ g (w, v)‖ = (c ^ (-1 - σ / 2) * (phi w.1 * phi w.2)) * (g ((w.1 / c) * v.2 - (w.2 / c) * v.1) * (phi v.1 * phi v.2))` using `fun v => by`. Rewrite using `[Real.norm_of_nonneg (domF_nonneg σ g hg0 _), domF_slice σ g w hc.ne' v]`. Simplify using `only [hfn]`. Rewrite using `[integral_const_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hmax]`. Clear the denominators using the available nonvanishing facts.
-/
theorem integrable_domF (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) (g : ℝ → ℝ) (hgm : Measurable g) (hg : Integrable g)
    (hg0 : ∀ x, 0 ≤ g x) : Integrable (domF σ g) := by
  have hsh := GlobalTheory.T.weighted_double_integral_bound g phi hgm measurable_phi hg integrable_phi hg0 phi_nonneg phi_le_one
  have hout := GlobalTheory.T.integrable_radial_cutoff_weight σ h0 h1
  have hm := measurable_domF σ g hgm
  have hc2 : ∀ w : ℝ × ℝ, w.1 ≠ 0 → 0 < w.1 ^ 2 + w.2 ^ 2 := fun w hw => by positivity
  have hαβ : ∀ w : ℝ × ℝ, w.1 ≠ 0 → w.2 ≠ 0 → w.1 / (w.1 ^ 2 + w.2 ^ 2) ≠ 0 ∧ w.2 / (w.1 ^ 2 + w.2 ^ 2) ≠ 0 :=
    fun w a b => ⟨div_ne_zero a (hc2 w a).ne', div_ne_zero b (hc2 w a).ne'⟩
  rw [Measure.volume_eq_prod, integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_ne_zero] with w hw
    obtain ⟨a, b⟩ := hw
    obtain ⟨i1, -⟩ := hsh _ _ (hαβ w a b).1 (hαβ w a b).2
    have := i1.const_mul ((w.1 ^ 2 + w.2 ^ 2) ^ (-1 - σ / 2) * (phi w.1 * phi w.2))
    refine this.congr (ae_of_all _ fun v => ?_)
    exact (domF_slice σ g w (hc2 w a).ne' v).symm
  · refine Integrable.mono' (hout.const_mul ((∫ x, g x) * (∫ x, phi x))) ?_ ?_
    · exact (hm.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
    · filter_upwards [ae_ne_zero] with w hw
      obtain ⟨a, b⟩ := hw
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      have hc := hc2 w a
      set c := w.1 ^ 2 + w.2 ^ 2 with hcdef
      obtain ⟨-, i2⟩ := hsh _ _ (hαβ w a b).1 (hαβ w a b).2
      have hmax : max |w.1 / c| |w.2 / c| = max |w.1| |w.2| / c := by
        rw [abs_div, abs_div, abs_of_pos hc, max_div_div_right hc.le]
      have hmpos : 0 < max |w.1| |w.2| := lt_max_of_lt_left (abs_pos.2 a)
      have hP : 0 ≤ c ^ (-1 - σ / 2) * (phi w.1 * phi w.2) :=
        mul_nonneg (Real.rpow_nonneg hc.le _) (mul_nonneg (phi_nonneg _) (phi_nonneg _))
      have hfn : ∀ v : ℝ × ℝ, ‖domF σ g (w, v)‖ = (c ^ (-1 - σ / 2) * (phi w.1 * phi w.2)) *
          (g ((w.1 / c) * v.2 - (w.2 / c) * v.1) * (phi v.1 * phi v.2)) := fun v => by
        rw [Real.norm_of_nonneg (domF_nonneg σ g hg0 _), domF_slice σ g w hc.ne' v]
      simp only [hfn]
      rw [integral_const_mul]
      calc _ ≤ (c ^ (-1 - σ / 2) * (phi w.1 * phi w.2)) *
            ((∫ x, g x) * (∫ x, phi x) / max |w.1 / c| |w.2 / c|) :=
            mul_le_mul_of_nonneg_left i2 hP
        _ = _ := by
            rw [hmax]
            field_simp

/- English proof (translation)
The claim follows from `ReciprocityTheory.GeometryOfNumbersTheory.measurePreserving_swapPi (volume : Measure ℝ)`.
-/
theorem transpose_mp : MeasurePreserving (fun (h : M22) (k i : Fin 2) => h i k) volume volume :=
  ReciprocityTheory.GeometryOfNumbersTheory.measurePreserving_swapPi (volume : Measure ℝ)

/- English proof (translation)
Establish `hD` using `integrable_domF σ h0 h1 g hgm hg hg0`. Establish `hmp` using `GlobalTheory.CompanionTheory.TwoByTwoMajorant.coord_mp.comp transpose_mp`. Use `(hmp.integrable_comp hD.aestronglyMeasurable).2 hD` as an intermediate fact. Use `this.congr (ae_of_all _ fun h => ?_)` and prove the remaining obligations. Simplify using `[domF, GlobalTheory.CompanionTheory.TwoByTwoMajorant.coord_apply, Matrix.det_fin_two]`.
-/
theorem mdom (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) (g : ℝ → ℝ) (hgm : Measurable g) (hg : Integrable g)
    (hg0 : ∀ x, 0 ≤ g x) :
    Integrable (fun h : M22 => g ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) * (h 0 0 ^ 2 + h 1 0 ^ 2) ^ (-1 - σ / 2) *
      (phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1)))) := by
  have hD := integrable_domF σ h0 h1 g hgm hg hg0
  have hmp := GlobalTheory.CompanionTheory.TwoByTwoMajorant.coord_mp.comp transpose_mp
  have := (hmp.integrable_comp hD.aestronglyMeasurable).2 hD
  refine this.congr (ae_of_all _ fun h => ?_)
  simp [domF, GlobalTheory.CompanionTheory.TwoByTwoMajorant.coord_apply, Matrix.det_fin_two]

/- English proof (translation)
Use `Measurable.norm (measurable_pi_lambda _ fun j => ?_)` and prove the remaining obligations. Apply the tactic sequence `exact GlobalTheory.CompanionTheory.GodementWeight.measurable_inv_entry 1 j`.
-/
theorem measurable_eta_norm : Measurable (fun h : M22 => ‖eta h‖) := by
  refine Measurable.norm (measurable_pi_lambda _ fun j => ?_)
  exact GlobalTheory.CompanionTheory.GodementWeight.measurable_inv_entry 1 j

/- English proof (translation)
Introduce `k hk σ h0 h1`. Use `⟨8, fun N hN => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `GlobalTheory.T.period_integrand_majorant k hk σ h0 h1 N hN`. Establish `hD` using `mdom σ h0 h1 (gk k σ) (measurable_gk k σ) (integrable_gk k (by omega) σ h1) (gk_nonneg k σ)`. Establish `hdet` using `GlobalTheory.CompanionTheory.GodementWeight.measurable_det_of`.

Establish `hm : Measurable (fun h : M22 => ‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) * ‖eta h‖ ^ (σ - 1) / (1 + ‖h‖) ^ N)`. Use `Measurable.div (Measurable.mul (Measurable.mul (GlobalTheory.CompanionTheory.GodementWeight.measurable_Wm_inv k).norm (hdet.abs.pow_const _)) (measurable_eta_norm.pow_const _)) ?_` and prove the remaining obligations. Use `fun_prop`. Use `Integrable.mono' (hD.const_mul |C|) hm.aestronglyMeasurable (Filter.Eventually.of_forall fun h => ?_)` and prove the remaining obligations. Establish `hnn : 0 ≤ gk k σ ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) * (h 0 0 ^ 2 + h 1 0 ^ 2) ^ (-1 - σ / 2) * (phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1)))` using `mul_nonneg (mul_nonneg (gk_nonneg _ _ _) (Real.rpow_nonneg (by positivity) _)) (mul_nonneg (mul_nonneg (phi_nonneg _) (phi_nonneg _)) (mul_nonneg (phi_nonneg _) (phi_nonneg _)))`.

Rewrite using `[Real.norm_of_nonneg (by positivity)]`. Distinguish the cases in `hd : (Matrix.of h).det = 0`. Establish `hinv : (Matrix.of h)⁻¹ = 0`. Apply `Matrix.nonsing_inv_apply_not_isUnit` to reduce the goal to its premises. Rewrite using `[hd]`.

Simplify using the standard rewrite rules. Establish `: ‖Wm k (Matrix.of h)⁻¹‖ = 0` using `by simp [hinv, Wm]`. Rewrite using `[this]`. Simplify using `using mul_nonneg (abs_nonneg C) hnn`. Use `(hC h hd).trans ?_` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_right (le_abs_self C) hnn`.
-/
theorem gint : ∀ k : ℕ, 3 ≤ k → ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    Integrable (fun h : M22 => ‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) *
      ‖eta h‖ ^ (σ - 1) / (1 + ‖h‖) ^ N) := by
  intro k hk σ h0 h1
  refine ⟨8, fun N hN => ?_⟩
  obtain ⟨C, hC⟩ := GlobalTheory.T.period_integrand_majorant k hk σ h0 h1 N hN
  have hD := mdom σ h0 h1 (gk k σ) (measurable_gk k σ) (integrable_gk k (by omega) σ h1) (gk_nonneg k σ)
  have hdet := GlobalTheory.CompanionTheory.GodementWeight.measurable_det_of
  have hm : Measurable (fun h : M22 => ‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) *
      ‖eta h‖ ^ (σ - 1) / (1 + ‖h‖) ^ N) := by
    refine Measurable.div (Measurable.mul (Measurable.mul
      (GlobalTheory.CompanionTheory.GodementWeight.measurable_Wm_inv k).norm (hdet.abs.pow_const _))
      (measurable_eta_norm.pow_const _)) ?_
    fun_prop
  refine Integrable.mono' (hD.const_mul |C|) hm.aestronglyMeasurable (Filter.Eventually.of_forall fun h => ?_)
  have hnn : 0 ≤ gk k σ ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) * (h 0 0 ^ 2 + h 1 0 ^ 2) ^ (-1 - σ / 2) *
      (phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1))) :=
    mul_nonneg (mul_nonneg (gk_nonneg _ _ _) (Real.rpow_nonneg (by positivity) _))
      (mul_nonneg (mul_nonneg (phi_nonneg _) (phi_nonneg _)) (mul_nonneg (phi_nonneg _) (phi_nonneg _)))
  rw [Real.norm_of_nonneg (by positivity)]
  by_cases hd : (Matrix.of h).det = 0
  · have hinv : (Matrix.of h)⁻¹ = 0 := by
      apply Matrix.nonsing_inv_apply_not_isUnit
      rw [hd]
      simp
    have : ‖Wm k (Matrix.of h)⁻¹‖ = 0 := by simp [hinv, Wm]
    rw [this]
    simpa using mul_nonneg (abs_nonneg C) hnn
  · refine (hC h hd).trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self C) hnn

/- English proof (translation)
Rewrite using `[norm_pos_iff]`. Introduce `he`. Establish `e0 : (Matrix.of h)⁻¹ 1 0 = 0` using `congrFun he 0`. Establish `e1 : (Matrix.of h)⁻¹ 1 1 = 0` using `congrFun he 1`. Establish `hm : (Matrix.of h)⁻¹ * Matrix.of h = 1` using `Matrix.nonsing_inv_mul _ (Ne.isUnit hd)`.

Use `congrFun (congrFun hm 1) 1` as an intermediate fact. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, e0, e1] at this`.
-/
theorem eta_ne_zero (h : M22) (hd : (Matrix.of h).det ≠ 0) : 0 < ‖eta h‖ := by
  rw [norm_pos_iff]
  intro he
  have e0 : (Matrix.of h)⁻¹ 1 0 = 0 := congrFun he 0
  have e1 : (Matrix.of h)⁻¹ 1 1 = 0 := congrFun he 1
  have hm : (Matrix.of h)⁻¹ * Matrix.of h = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit hd)
  have := congrFun (congrFun hm 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, e0, e1] at this

/- English proof (translation)
The claim follows from `|(t : ℝ)| ^ (s.re - 1) * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(1 : ℝ) / 2) * ‖innB Ψ h (t : ℝ)⁻¹‖) := by have ht : 0 < |(t : ℝ)| := abs_pos.2 t.ne_zero have h1 : |(t : ℝ)| ^ (s.re - 1) = |(t : ℝ)| ^ s.re * |(t : ℝ)|⁻¹ := by rw [Real.rpow_sub ht, Real.rpow_one, div_eq …`.
-/
theorem norm_integrand (k : ℕ) (Ψ : M23 → ℂ) (δ : Bool) (s : ℂ) (t : ℝˣ) (h : M22) :
    ‖chR δ s t * sg t * (((|(t : ℝ)|)⁻¹ : ℝ) : ℂ) *
      (Wm k (Matrix.of h)⁻¹ * sg (Matrix.of h).det * ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
        innB Ψ h (t : ℝ)⁻¹)‖ =
      |(t : ℝ)| ^ (s.re - 1) * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(1 : ℝ) / 2) *
        ‖innB Ψ h (t : ℝ)⁻¹‖) := by
  have ht : 0 < |(t : ℝ)| := abs_pos.2 t.ne_zero
  have h1 : |(t : ℝ)| ^ (s.re - 1) = |(t : ℝ)| ^ s.re * |(t : ℝ)|⁻¹ := by
    rw [Real.rpow_sub ht, Real.rpow_one, div_eq_mul_inv]
  simp only [norm_mul, GlobalTheory.CompanionTheory.PrimalInt.norm_sg, GlobalTheory.CompanionTheory.PrimalInt.norm_chR, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (Matrix.of h).det) _),
    abs_inv, abs_abs, h1]
  ring

/- English proof (translation)
Introduce `hIbp k hk Φ δ s hs0 hs1 u`. Take `⟨N₀, hG⟩` from `gint k hk s.re hs0 hs1`. Take `⟨K, hK⟩` from `GlobalTheory.T.mult_integral_power_bound s.re hs0 hs1 (N₀ + 1) (by omega)`. Establish `hGN` using `hG (N₀ + 1) (by omega)`. Take `⟨C₁, hC₁⟩` from `hIbp (N₀ + 1)`.

Use `set N := N₀ + 1 with hNdef`. Use `set Ψ : Sw := rtS (cyc u) Φ with hΨdef`. Establish `hΨ : B.rt (cyc u) ⇑Φ = ⇑Ψ` using `(rtS_apply _ _).symm`. Rewrite using `[hΨ]`. Use `set B : ℝ := 2 ^ (N + 8) * (Finset.Iic ((N + 8, N) : ℕ × ℕ)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Ψ with hBdef`.

Establish `hB : ∀ n ≤ N, ∀ X : M23, (1 + ‖X‖) ^ (N + 8) * ‖iteratedFDeriv ℝ n (⇑Ψ) X‖ ≤ B` using `fun n hn X => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N + 8, N)) le_rfl hn Ψ X`. Establish `hInn : ∀ (h : M22) (t : ℝˣ), (Matrix.of h).det ≠ 0 → ‖innB (⇑Ψ) h (t : ℝ)⁻¹‖ ≤ |C₁ * B| * |(Matrix.of h).det|⁻¹ / ((1 + ‖h‖) ^ N * (1 + |(t : ℝ)⁻¹| * ‖eta h‖) ^ N)`. Introduce `h t hd`. Use `(hC₁ (⇑Ψ) B (Ψ.smooth ⊤) hB h _ hd).trans ?_` and prove the remaining obligations. Use `gcongr`.

Conclude with `le_abs_self _`. Establish `hmeas : Measurable (fun p : ℝˣ × M22 => chR δ s p.1 * sg p.1 * (((|(p.1 : ℝ)|)⁻¹ : ℝ) : ℂ) * (Wm k (Matrix.of p.2)⁻¹ * sg (Matrix.of p.2).det * ((|(Matrix.of p.2).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * innB (⇑Ψ) p.2 (p.1 : ℝ)⁻¹))`. Establish `hv : Measurable (fun p : ℝˣ × M22 => ((p.1 : ℝˣ) : ℝ))` using `GlobalTheory.CompanionTheory.PrimalInt.measurable_val.comp measurable_fst`. Use `(((((GlobalTheory.CompanionTheory.PrimalInt.measurable_chR δ s).comp measurable_fst).mul (GlobalTheory.CompanionTheory.GodementWeight.measurable_sg hv)).mul ?_).mul (((GlobalTheory.CompanionTheory.GodementWeight.measurable_weight k).comp measurable_snd).mul (measurable_innB _ Ψ.c …` and prove the remaining obligations. Conclude with `Complex.measurable_ofReal.comp (hv.abs.inv)`.

Establish `hW0 : ∀ h : M22, (Matrix.of h).det = 0 → Wm k (Matrix.of h)⁻¹ = 0`. Introduce `h hd`. Establish `hinv : (Matrix.of h)⁻¹ = 0`. Apply `Matrix.nonsing_inv_apply_not_isUnit` to reduce the goal to its premises. Rewrite using `[hd]`.

Simplify using the standard rewrite rules. Simplify using `[hinv, Wm]`. Establish `hnorm` using `fun (t : ℝˣ) (h : M22) => norm_integrand k (⇑Ψ) δ s t h`. Establish `hpt : ∀ (h : M22) (t : ℝˣ), (Matrix.of h).det ≠ 0 → |(t : ℝ)| ^ (s.re - 1) * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(1 : ℝ) / 2) * ‖innB (⇑Ψ) h (t : ℝ)⁻¹‖) ≤ (|C₁ * B| * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) / (1 + ‖h‖) ^ N)) * (|(t : ℝ)| ^ (s. …`. Introduce `h t hd`.

Establish `hA : 0 < |(Matrix.of h).det|` using `abs_pos.2 hd`. Establish `h32 : |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) = |(Matrix.of h).det| ^ (-(1 : ℝ) / 2) * |(Matrix.of h).det|⁻¹`. Rewrite using `[← Real.rpow_neg_one, ← Real.rpow_add hA]`. Evaluate the numerical expressions. Establish `hb` using `hInn h t hd`.

Establish `hc : 0 ≤ |(t : ℝ)| ^ (s.re - 1) * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(1 : ℝ) / 2))`. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h32]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[integrable_prod_iff' hmeas.aestronglyMeasurable]`. Use `⟨Filter.Eventually.of_forall fun h => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hd : (Matrix.of h).det = 0`. Simplify using `only [hW0 h hd, zero_mul, mul_zero]`. Conclude with `integrable_zero _ _ _`.

Use `Integrable.mono' (((hK _ (eta_ne_zero h hd)).1).const_mul (|C₁ * B| * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) / (1 + ‖h‖) ^ N))) ?_ ?_` and prove the remaining obligations. Conclude with `(hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable`. Conclude with `Filter.Eventually.of_forall fun t => by`. Use `hpt h t hd` as an intermediate fact. Rewrite `this` using `[← hnorm t h]`.

Conclude with `this`. Use `Integrable.mono' (hGN.const_mul (|C₁ * B| * |K|)) ?_ ?_` and prove the remaining obligations. Conclude with `(hmeas.norm.stronglyMeasurable.integral_prod_left' (μ := mulR)).aestronglyMeasurable`. Use `Filter.Eventually.of_forall fun h => ?_` and prove the remaining obligations. Rewrite using `[Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]`.

Distinguish the cases in `hd : (Matrix.of h).det = 0`. Simplify using `only [hW0 h hd, zero_mul, mul_zero, norm_zero, integral_zero, norm_zero]`. Simplify using the standard rewrite rules. Establish `hq` using `eta_ne_zero h hd`. Take `⟨i1, i2⟩` from `hK _ hq`.

Use `set E : ℝ := ‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) / (1 + ‖h‖) ^ N with hE`. Establish `hE0 : 0 ≤ E` using `by positivity`. Establish `hqp : 0 ≤ ‖eta h‖ ^ (s.re - 1)` using `Real.rpow_nonneg hq.le _`. Combine the equalities or inequalities in the displayed calculation. Use `integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) (i1.const_mul _) (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations.

Use `hpt h t hd` as an intermediate fact. Rewrite `this` using `[← hnorm t h]`. Conclude with `this`. Use `_ = (|C₁ * B| * E) * ∫ t : ℝˣ, |(t : ℝ)| ^ (s.re - 1) / (1 + |(t : ℝ)⁻¹| * ‖eta h‖) ^ N ∂mulR := integral_const_mul _ _`. Use `_ ≤ (|C₁ * B| * E) * (K * ‖eta h‖ ^ (s.re - 1)) := by gcongr`.

Use `_ ≤ (|C₁ * B| * E) * (|K| * ‖eta h‖ ^ (s.re - 1)) := by gcongr`. Conclude with `le_abs_self _`. Use `_ = _ := by`. Rewrite using `[hE]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : IbpBound → UnipotentJointIntegrability := by
  intro hIbp k hk Φ δ s hs0 hs1 u
  obtain ⟨N₀, hG⟩ := gint k hk s.re hs0 hs1
  obtain ⟨K, hK⟩ := GlobalTheory.T.mult_integral_power_bound s.re hs0 hs1 (N₀ + 1) (by omega)
  have hGN := hG (N₀ + 1) (by omega)
  obtain ⟨C₁, hC₁⟩ := hIbp (N₀ + 1)
  set N := N₀ + 1 with hNdef
  set Ψ : Sw := rtS (cyc u) Φ with hΨdef
  have hΨ : B.rt (cyc u) ⇑Φ = ⇑Ψ := (rtS_apply _ _).symm
  rw [hΨ]
  set B : ℝ := 2 ^ (N + 8) * (Finset.Iic ((N + 8, N) : ℕ × ℕ)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Ψ with hBdef
  have hB : ∀ n ≤ N, ∀ X : M23, (1 + ‖X‖) ^ (N + 8) * ‖iteratedFDeriv ℝ n (⇑Ψ) X‖ ≤ B :=
    fun n hn X => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N + 8, N)) le_rfl hn Ψ X
  have hInn : ∀ (h : M22) (t : ℝˣ), (Matrix.of h).det ≠ 0 →
      ‖innB (⇑Ψ) h (t : ℝ)⁻¹‖ ≤ |C₁ * B| * |(Matrix.of h).det|⁻¹ /
        ((1 + ‖h‖) ^ N * (1 + |(t : ℝ)⁻¹| * ‖eta h‖) ^ N) := by
    intro h t hd
    refine (hC₁ (⇑Ψ) B (Ψ.smooth ⊤) hB h _ hd).trans ?_
    gcongr
    exact le_abs_self _
  have hmeas : Measurable (fun p : ℝˣ × M22 => chR δ s p.1 * sg p.1 * (((|(p.1 : ℝ)|)⁻¹ : ℝ) : ℂ) *
      (Wm k (Matrix.of p.2)⁻¹ * sg (Matrix.of p.2).det * ((|(Matrix.of p.2).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
        innB (⇑Ψ) p.2 (p.1 : ℝ)⁻¹)) := by
    have hv : Measurable (fun p : ℝˣ × M22 => ((p.1 : ℝˣ) : ℝ)) :=
      GlobalTheory.CompanionTheory.PrimalInt.measurable_val.comp measurable_fst
    refine (((((GlobalTheory.CompanionTheory.PrimalInt.measurable_chR δ s).comp measurable_fst).mul
      (GlobalTheory.CompanionTheory.GodementWeight.measurable_sg hv)).mul ?_).mul
      (((GlobalTheory.CompanionTheory.GodementWeight.measurable_weight k).comp measurable_snd).mul
        (measurable_innB _ Ψ.continuous)))
    exact Complex.measurable_ofReal.comp (hv.abs.inv)
  have hW0 : ∀ h : M22, (Matrix.of h).det = 0 → Wm k (Matrix.of h)⁻¹ = 0 := by
    intro h hd
    have hinv : (Matrix.of h)⁻¹ = 0 := by
      apply Matrix.nonsing_inv_apply_not_isUnit
      rw [hd]
      simp
    simp [hinv, Wm]
  have hnorm := fun (t : ℝˣ) (h : M22) => norm_integrand k (⇑Ψ) δ s t h

  have hpt : ∀ (h : M22) (t : ℝˣ), (Matrix.of h).det ≠ 0 →
      |(t : ℝ)| ^ (s.re - 1) * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(1 : ℝ) / 2) *
        ‖innB (⇑Ψ) h (t : ℝ)⁻¹‖) ≤
      (|C₁ * B| * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) / (1 + ‖h‖) ^ N)) *
        (|(t : ℝ)| ^ (s.re - 1) / (1 + |(t : ℝ)⁻¹| * ‖eta h‖) ^ N) := by
    intro h t hd
    have hA : 0 < |(Matrix.of h).det| := abs_pos.2 hd
    have h32 : |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) =
        |(Matrix.of h).det| ^ (-(1 : ℝ) / 2) * |(Matrix.of h).det|⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hA]
      norm_num
    have hb := hInn h t hd
    have hc : 0 ≤ |(t : ℝ)| ^ (s.re - 1) * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(1 : ℝ) / 2)) := by
      positivity
    calc _ = |(t : ℝ)| ^ (s.re - 1) * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(1 : ℝ) / 2)) *
          ‖innB (⇑Ψ) h (t : ℝ)⁻¹‖ := by ring
      _ ≤ |(t : ℝ)| ^ (s.re - 1) * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(1 : ℝ) / 2)) *
          (|C₁ * B| * |(Matrix.of h).det|⁻¹ /
            ((1 + ‖h‖) ^ N * (1 + |(t : ℝ)⁻¹| * ‖eta h‖) ^ N)) := mul_le_mul_of_nonneg_left hb hc
      _ = _ := by
        rw [h32]
        field_simp
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun h => ?_, ?_⟩
  · by_cases hd : (Matrix.of h).det = 0
    · simp only [hW0 h hd, zero_mul, mul_zero]
      exact integrable_zero _ _ _
    · refine Integrable.mono' (((hK _ (eta_ne_zero h hd)).1).const_mul
        (|C₁ * B| * (‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) / (1 + ‖h‖) ^ N))) ?_ ?_
      · exact (hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun t => by
          have := hpt h t hd
          rw [← hnorm t h] at this
          exact this
  · refine Integrable.mono' (hGN.const_mul (|C₁ * B| * |K|)) ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_left' (μ := mulR)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun h => ?_
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      by_cases hd : (Matrix.of h).det = 0
      · simp only [hW0 h hd, zero_mul, mul_zero, norm_zero, integral_zero, norm_zero]
        simp
      · have hq := eta_ne_zero h hd
        obtain ⟨i1, i2⟩ := hK _ hq
        set E : ℝ := ‖Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) / (1 + ‖h‖) ^ N with hE
        have hE0 : 0 ≤ E := by positivity
        have hqp : 0 ≤ ‖eta h‖ ^ (s.re - 1) := Real.rpow_nonneg hq.le _
        calc ∫ t : ℝˣ, ‖_‖ ∂mulR ≤ ∫ t : ℝˣ, (|C₁ * B| * E) *
              (|(t : ℝ)| ^ (s.re - 1) / (1 + |(t : ℝ)⁻¹| * ‖eta h‖) ^ N) ∂mulR := by
              refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
                (i1.const_mul _) (Filter.Eventually.of_forall fun t => ?_)
              have := hpt h t hd
              rw [← hnorm t h] at this
              exact this
          _ = (|C₁ * B| * E) * ∫ t : ℝˣ, |(t : ℝ)| ^ (s.re - 1) / (1 + |(t : ℝ)⁻¹| * ‖eta h‖) ^ N ∂mulR :=
              integral_const_mul _ _
          _ ≤ (|C₁ * B| * E) * (K * ‖eta h‖ ^ (s.re - 1)) := by gcongr
          _ ≤ (|C₁ * B| * E) * (|K| * ‖eta h‖ ^ (s.re - 1)) := by
              gcongr
              exact le_abs_self _
          _ = _ := by
              rw [hE]
              ring

end GlobalTheory.CompanionTheory.PerUInt
