import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.Development
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.BesselUnitaryEquivHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure

open MeasureTheory Set
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.BICNZ

open Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.MainNotions.S.Pv.BetaCut

variable {k r : ℕ}

/- English proof (translation)
Establish `: IsFiniteMeasureOnCompacts μ` using `⟨fun K hK => h.finite_compact K hK⟩`. Use `infer_instance`.
-/
theorem lim_sf {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

def invT (x : Mt k r) : Mt k r := ((Matrix.of x)⁻¹ : Mat k r)

def mul3 (p : Mt k r × Mt k r × Mt k r) : Mt k r := (Matrix.of p.1 * Matrix.of p.2.1 * Matrix.of p.2.2 : Mat k r)

def aDilT (t : ℝ) : Mt k r := aDil k r t

/- English proof (translation)
Establish `hid : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r))` using `continuous_id`. Establish `hd : Measurable (fun x : Mt k r => (Matrix.of x).det)` using `(Continuous.matrix_det hid).measurable`. Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Establish `e : ∀ x : Mt k r, invT x i j = ((Matrix.of x).det)⁻¹ * (Matrix.of x).adjugate i j`. Introduce `x`.

Use `show ((Matrix.of x)⁻¹ : Mat k r) i j = _`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv']`. Both sides reduce to the same expression. Repeatedly rewrite using `[e]`. Establish `ha : Continuous (fun x : Mt k r => (Matrix.of x).adjugate i j)` using `(continuous_apply j).comp ((continuous_apply i).comp (Continuous.matrix_adjugate hid))`.

Conclude with `(measurable_inv.comp hd).mul ha.measurable`.
-/
theorem lim_measurable_inv : Measurable (invT (k := k) (r := r)) := by
  have hid : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hd : Measurable (fun x : Mt k r => (Matrix.of x).det) := (Continuous.matrix_det hid).measurable
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have e : ∀ x : Mt k r, invT x i j = ((Matrix.of x).det)⁻¹ * (Matrix.of x).adjugate i j := by
    intro x
    show ((Matrix.of x)⁻¹ : Mat k r) i j = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rfl
  simp_rw [e]
  have ha : Continuous (fun x : Mt k r => (Matrix.of x).adjugate i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (Continuous.matrix_adjugate hid))
  exact (measurable_inv.comp hd).mul ha.measurable

/- English proof (translation)
Establish `h : Continuous (mul3 (k` using `k) (r := r)) := by`. Unfold `mul3`. Conclude with `(continuous_fst.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul (continuous_snd.comp continuous_snd)`. Conclude with `h.measurable`.
-/
theorem measurable_triple_product : Measurable (mul3 (k := k) (r := r)) := by
  have h : Continuous (mul3 (k := k) (r := r)) := by
    unfold mul3
    exact (continuous_fst.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul
      (continuous_snd.comp continuous_snd)
  exact h.measurable

/- English proof (translation)
Use `measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Distinguish the cases in `h1 : i.val < r`. Establish `e : (fun t : ℝ => aDilT (k` using `k) (r := r) t i i) = fun t => ((t ^ (r - i.val) : ℝ) : ℂ) := by`.

Use function extensionality and compare the values at `t`. Simplify using `[aDilT, aDil, h1]`. Rewrite using `[e]`. Conclude with `Complex.measurable_ofReal.comp (measurable_id.pow_const _)`. Distinguish the cases in `h2 : i.val ≤ r + k`.

Establish `e : (fun t : ℝ => aDilT (k` using `k) (r := r) t i i) = fun _ => (1 : ℂ) := by`. Use function extensionality and compare the values at `t`. Simplify using `[aDilT, aDil, h1, h2]`. Rewrite using `[e]`. Conclude with `measurable_const`.

Establish `e : (fun t : ℝ => aDilT (k` using `k) (r := r) t i i) = fun t => (((t ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ) := by`. Use function extensionality and compare the values at `t`. Simplify using `[aDilT, aDil, h1, h2]`. Rewrite using `[e]`. Conclude with `Complex.measurable_ofReal.comp (measurable_id.pow_const _).inv`.

Establish `e : (fun t : ℝ => aDilT (k` using `k) (r := r) t i j) = fun _ => (0 : ℂ) := by`. Use function extensionality and compare the values at `t`. Simplify using `[aDilT, aDil, hij]`. Rewrite using `[e]`. Conclude with `measurable_const`.
-/
theorem lim_measurable_aDil : Measurable (aDilT (k := k) (r := r)) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  by_cases hij : i = j
  · subst hij
    by_cases h1 : i.val < r
    · have e : (fun t : ℝ => aDilT (k := k) (r := r) t i i) = fun t => ((t ^ (r - i.val) : ℝ) : ℂ) := by
        funext t; simp [aDilT, aDil, h1]
      rw [e]; exact Complex.measurable_ofReal.comp (measurable_id.pow_const _)
    · by_cases h2 : i.val ≤ r + k
      · have e : (fun t : ℝ => aDilT (k := k) (r := r) t i i) = fun _ => (1 : ℂ) := by
          funext t; simp [aDilT, aDil, h1, h2]
        rw [e]; exact measurable_const
      · have e : (fun t : ℝ => aDilT (k := k) (r := r) t i i) =
            fun t => (((t ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ) := by
          funext t; simp [aDilT, aDil, h1, h2]
        rw [e]; exact Complex.measurable_ofReal.comp (measurable_id.pow_const _).inv
  · have e : (fun t : ℝ => aDilT (k := k) (r := r) t i j) = fun _ => (0 : ℂ) := by
      funext t; simp [aDilT, aDil, hij]
    rw [e]; exact measurable_const

def limDil (p : ℝ × (Mt k r × Mt k r)) : ℝ × (Mt k r × Mt k r) :=
  (p.1, (p.2.1, conjM (aDil k r p.1) p.2.2))

/- English proof (translation)
Establish `e : (fun p : ℝ × (Mt k r × Mt k r) => conjM (aDil k r p.1) p.2.2) = mul3 ∘ (fun p : ℝ × (Mt k r × Mt k r) => (aDilT p.1, p.2.2, invT (aDilT (k` using `k) (r := r) p.1))) := by`. Use function extensionality and compare the values at `p`. Simplify using `only [Function.comp, mul3, invT, aDilT, conjM]`. Both sides reduce to the same expression. Establish `hc : Measurable (fun p : ℝ × (Mt k r × Mt k r) => conjM (aDil k r p.1) p.2.2)`.

Rewrite using `[e]`. Conclude with `measurable_triple_product.comp ((lim_measurable_aDil.comp measurable_fst).prodMk ((measurable_snd.comp measurable_snd).prodMk ((lim_measurable_inv.comp lim_measurable_aDil).comp measurable_fst)))`. Conclude with `measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk hc)`.
-/
theorem lim_measurable_dil : Measurable (limDil (k := k) (r := r)) := by
  have e : (fun p : ℝ × (Mt k r × Mt k r) => conjM (aDil k r p.1) p.2.2) =
      mul3 ∘ (fun p : ℝ × (Mt k r × Mt k r) => (aDilT p.1, p.2.2, invT (aDilT (k := k) (r := r) p.1))) := by
    funext p
    simp only [Function.comp, mul3, invT, aDilT, conjM]
    rfl
  have hc : Measurable (fun p : ℝ × (Mt k r × Mt k r) => conjM (aDil k r p.1) p.2.2) := by
    rw [e]
    exact measurable_triple_product.comp ((lim_measurable_aDil.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_snd).prodMk ((lim_measurable_inv.comp lim_measurable_aDil).comp measurable_fst)))
  exact measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk hc)

/- English proof (translation)
Use `⟨lim_measurable_dil, ?_⟩` and prove the remaining obligations. Use extensionality with `s hs`. Establish `hw : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ kap k r))` using `ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)`. Rewrite using `[Measure.map_apply lim_measurable_dil hs, Measure.prod_apply (lim_measurable_dil hs), Measure.prod_apply hs, lintegral_withDensity_eq_lintegral_mul _ hw (measurable_measure_prodMk_left (lim_measurable_dil hs))]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht`. Establish `ht' : (0 : ℝ) < t` using `ht`. Establish `hcm : Measurable (conjM (k` using `k) (r := r) (aDil k r t)) := (BesselUnitaryEquiv.continuous_conjM _).measurable`. Establish `hm : Measurable (Prod.map (id : Mt k r → Mt k r) (conjM (aDil k r t)))` using `measurable_id.prodMap hcm`. Establish `hpre : Prod.mk t ⁻¹' (limDil (k` using `k) (r := r) ⁻¹' s) = Prod.map id (conjM (aDil k r t)) ⁻¹' (Prod.mk t ⁻¹' s) := rfl`.

Simplify using `only [Pi.mul_apply]`. Rewrite using `[hpre, ← Measure.map_apply hm (measurable_prodMk_left hs), ← Measure.map_prod_map _ _ measurable_id hcm, Measure.map_id, hJ t ht', Measure.prod_smul_right, Measure.smul_apply, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal …`.
-/
theorem lim_dil_mp (μW μN : Measure (Mt k r)) [SigmaFinite μW] [SigmaFinite μN]
    (hJ : ∀ t : ℝ, 0 < t → μN.map (conjM (aDil k r t)) = ENNReal.ofReal ((t ^ kap k r)⁻¹) • μN) :
    MeasurePreserving (limDil (k := k) (r := r))
      (((volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal (t ^ kap k r))).prod (μW.prod μN))
      ((volume.restrict (Ioi (0 : ℝ))).prod (μW.prod μN)) := by
  refine ⟨lim_measurable_dil, ?_⟩
  ext s hs
  have hw : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ kap k r)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  rw [Measure.map_apply lim_measurable_dil hs, Measure.prod_apply (lim_measurable_dil hs), Measure.prod_apply hs,
    lintegral_withDensity_eq_lintegral_mul _ hw (measurable_measure_prodMk_left (lim_measurable_dil hs))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : (0 : ℝ) < t := ht
  have hcm : Measurable (conjM (k := k) (r := r) (aDil k r t)) := (BesselUnitaryEquiv.continuous_conjM _).measurable
  have hm : Measurable (Prod.map (id : Mt k r → Mt k r) (conjM (aDil k r t))) := measurable_id.prodMap hcm
  have hpre : Prod.mk t ⁻¹' (limDil (k := k) (r := r) ⁻¹' s) =
      Prod.map id (conjM (aDil k r t)) ⁻¹' (Prod.mk t ⁻¹' s) := rfl
  simp only [Pi.mul_apply]
  rw [hpre, ← Measure.map_apply hm (measurable_prodMk_left hs), ← Measure.map_prod_map _ _ measurable_id hcm,
    Measure.map_id, hJ t ht', Measure.prod_smul_right, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

/- English proof (translation)
Use `set μ := μW.prod μN with hμ`. Use `set ρ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hρ`. Use `set E : Mt k r × Mt k r → ℂ := fun x => B x * Complex.exp (Complex.I * (Λ x.2 : ℂ)) with hE`. Use `set K : ℝ × (Mt k r × Mt k r) → ℂ := fun p => ((χ p.1 : ℝ) : ℂ) * E p.2 with hK`. Use `set G : ℝ × (Mt k r × Mt k r) → ℂ := fun p => ((χ p.1 * p.1 ^ kap k r : ℝ) : ℂ) * B (p.2.1, conjM (aDil k r p.1) p.2.2) * Complex.exp (Complex.I * ((Λ p.2.2 * p.1 : ℝ) : ℂ)) with hG`.

Use `set w : ℝ → NNReal := fun t => (t ^ kap k r).toNNReal with hw`. Establish `hwm : Measurable w` using `measurable_real_toNNReal.comp (measurable_id.pow_const _)`. Establish `hχi : Integrable (fun t => ((χ t : ℝ) : ℂ)) ρ` using `((hχc.integrable_of_hasCompactSupport hχs).ofReal).integrableOn`. Establish `hKi : Integrable K (ρ.prod μ)` using `hχi.mul_prod hB`. Establish `hMP` using `lim_dil_mp μW μN hJ`.

Establish `hKD : Integrable (K ∘ limDil) ((ρ.withDensity (fun t => ENNReal.ofReal (t ^ kap k r))).prod μ)` using `(hMP.integrable_comp hKi.aestronglyMeasurable).2 hKi`. Establish `hKDint : ∫ p, (K ∘ limDil) p ∂((ρ.withDensity (fun t => ENNReal.ofReal (t ^ kap k r))).prod μ) = ∫ p, K p ∂(ρ.prod μ)`. Use `integral_map hMP.measurable.aemeasurable (hMP.map_eq.symm ▸ hKi.aestronglyMeasurable)` as an intermediate fact. Rewrite `this` using `[hMP.map_eq]`. Conclude with `this.symm`.

Establish `hdens : (ρ.withDensity (fun t => ENNReal.ofReal (t ^ kap k r))).prod μ = (ρ.prod μ).withDensity (fun p => ((w p.1 : NNReal) : ℝ≥0∞))` using `prod_withDensity_left (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))`. Establish `hwm' : Measurable (fun p : ℝ × (Mt k r × Mt k r) => w p.1)` using `hwm.comp measurable_fst`. Rewrite `hKD`, `hKDint` using `[hdens]`. Rewrite `hKD` using `[integrable_withDensity_iff_integrable_smul hwm']`. Rewrite `hKDint` using `[integral_withDensity_eq_integral_smul hwm']`.

Establish `hae : ∀ᵐ p ∂(ρ.prod μ), w p.1 • (K ∘ limDil) p = G p`. Establish `a1 : ∀ᵐ p ∂(ρ.prod μ), p.1 ∈ Ioi (0 : ℝ)` using `Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)`. Establish `a2 : ∀ᵐ p ∂(ρ.prod μ), p.2.2 ∈ Nn` using `(Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_snd).ae hN`. Use `filter_upwards [a1, a2] with p hp1 hp2`. Establish `hp1' : (0 : ℝ) < p.1` using `hp1`.

Establish `hl` using `hΛ p.1 hp1' p.2.2 hp2`. Establish `hw1 : ((w p.1 : NNReal) : ℝ) = p.1 ^ kap k r` using `Real.coe_toNNReal _ (by positivity)`. Simplify using `only [hG, hK, hE, Function.comp, limDil, hl]`. Rewrite using `[NNReal.smul_def, hw1, Complex.real_smul]`. Use `push_cast`.

Put the polynomial expressions in normal form. Establish `hGi : Integrable G (ρ.prod μ)` using `hKD.congr hae`. Establish `hGint : ∫ p, G p ∂(ρ.prod μ) = ∫ x, E x ∂μ`. Rewrite using `[← integral_congr_ae hae, hKDint, hK, integral_prod_mul (fun t => ((χ t : ℝ) : ℂ)) E, integral_complex_ofReal]`. Establish `: ∫ t in Ioi (0 : ℝ), χ t = 1`.

Rewrite using `[setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun t ht => hχ0 t (not_lt.mp ht))]`. Conclude with `hχ1`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `hR : ρ.prod μ = (volume.prod μ).restrict (Ioi (0 : ℝ) ×ˢ univ)`.

Rewrite using `[← Measure.prod_restrict, Measure.restrict_univ]`. Establish `hz : ∀ p : ℝ × (Mt k r × Mt k r), p ∉ Ioi (0 : ℝ) ×ˢ (univ : Set (Mt k r × Mt k r)) → G p = 0`. Introduce `p hp`. Establish `: p.1 ≤ 0`. Assume the negation of the conclusion as `hc`.

Conclude with `hp ⟨not_le.mp hc, mem_univ _⟩`. Simplify using `[hG, hχ0 p.1 this]`. Establish `hGv : Integrable G (volume.prod μ)`. Use `(integrableOn_iff_integrable_of_support_subset ?_).1 (hR ▸ hGi)` and prove the remaining obligations. Introduce `p hp`.

Assume the negation of the conclusion as `hc`. Conclude with `hp (hz p hc)`. Establish `hGvint : ∫ p, G p ∂(volume.prod μ) = ∫ p, G p ∂(ρ.prod μ)`. Rewrite using `[hR, setIntegral_eq_integral_of_forall_compl_eq_zero hz]`. Establish `hF : Integrable (fun z : (Mt k r × Mt k r) × ℝ => G z.swap) (μ.prod volume)` using `hGv.swap`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem lim_dil_fubini (μW μN : Measure (Mt k r)) [SigmaFinite μW] [SigmaFinite μN]
    (hJ : ∀ t : ℝ, 0 < t → μN.map (conjM (aDil k r t)) = ENNReal.ofReal ((t ^ kap k r)⁻¹) • μN)
    (χ : ℝ → ℝ) (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ t : ℝ, t ≤ 0 → χ t = 0)
    (hχ1 : ∫ t, χ t = 1) (Nn : Set (Mt k r)) (hN : ∀ᵐ n ∂μN, n ∈ Nn)
    (Λ : Mt k r → ℝ) (hΛ : ∀ t : ℝ, 0 < t → ∀ n ∈ Nn, Λ (conjM (aDil k r t) n) = t * Λ n)
    (B : Mt k r × Mt k r → ℂ)
    (hB : Integrable (fun x => B x * Complex.exp (Complex.I * (Λ x.2 : ℂ))) (μW.prod μN)) :
    ∫ x, (∫ t : ℝ, ((χ t * t ^ kap k r : ℝ) : ℂ) * B (x.1, conjM (aDil k r t) x.2) *
        Complex.exp (Complex.I * ((Λ x.2 * t : ℝ) : ℂ))) ∂(μW.prod μN) =
      ∫ x, B x * Complex.exp (Complex.I * (Λ x.2 : ℂ)) ∂(μW.prod μN) := by
  set μ := μW.prod μN with hμ
  set ρ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hρ
  set E : Mt k r × Mt k r → ℂ := fun x => B x * Complex.exp (Complex.I * (Λ x.2 : ℂ)) with hE
  set K : ℝ × (Mt k r × Mt k r) → ℂ := fun p => ((χ p.1 : ℝ) : ℂ) * E p.2 with hK
  set G : ℝ × (Mt k r × Mt k r) → ℂ := fun p => ((χ p.1 * p.1 ^ kap k r : ℝ) : ℂ) *
    B (p.2.1, conjM (aDil k r p.1) p.2.2) * Complex.exp (Complex.I * ((Λ p.2.2 * p.1 : ℝ) : ℂ)) with hG
  set w : ℝ → NNReal := fun t => (t ^ kap k r).toNNReal with hw
  have hwm : Measurable w := measurable_real_toNNReal.comp (measurable_id.pow_const _)
  have hχi : Integrable (fun t => ((χ t : ℝ) : ℂ)) ρ :=
    ((hχc.integrable_of_hasCompactSupport hχs).ofReal).integrableOn
  have hKi : Integrable K (ρ.prod μ) := hχi.mul_prod hB
  have hMP := lim_dil_mp μW μN hJ
  have hKD : Integrable (K ∘ limDil) ((ρ.withDensity (fun t => ENNReal.ofReal (t ^ kap k r))).prod μ) :=
    (hMP.integrable_comp hKi.aestronglyMeasurable).2 hKi
  have hKDint : ∫ p, (K ∘ limDil) p ∂((ρ.withDensity (fun t => ENNReal.ofReal (t ^ kap k r))).prod μ) =
      ∫ p, K p ∂(ρ.prod μ) := by
    have := integral_map hMP.measurable.aemeasurable (hMP.map_eq.symm ▸ hKi.aestronglyMeasurable)
    rw [hMP.map_eq] at this
    exact this.symm
  have hdens : (ρ.withDensity (fun t => ENNReal.ofReal (t ^ kap k r))).prod μ =
      (ρ.prod μ).withDensity (fun p => ((w p.1 : NNReal) : ℝ≥0∞)) :=
    prod_withDensity_left (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
  have hwm' : Measurable (fun p : ℝ × (Mt k r × Mt k r) => w p.1) := hwm.comp measurable_fst
  rw [hdens] at hKD hKDint
  rw [integrable_withDensity_iff_integrable_smul hwm'] at hKD
  rw [integral_withDensity_eq_integral_smul hwm'] at hKDint

  have hae : ∀ᵐ p ∂(ρ.prod μ), w p.1 • (K ∘ limDil) p = G p := by
    have a1 : ∀ᵐ p ∂(ρ.prod μ), p.1 ∈ Ioi (0 : ℝ) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
    have a2 : ∀ᵐ p ∂(ρ.prod μ), p.2.2 ∈ Nn :=
      (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_snd).ae hN
    filter_upwards [a1, a2] with p hp1 hp2
    have hp1' : (0 : ℝ) < p.1 := hp1
    have hl := hΛ p.1 hp1' p.2.2 hp2
    have hw1 : ((w p.1 : NNReal) : ℝ) = p.1 ^ kap k r := Real.coe_toNNReal _ (by positivity)
    simp only [hG, hK, hE, Function.comp, limDil, hl]
    rw [NNReal.smul_def, hw1, Complex.real_smul]
    push_cast
    ring_nf
  have hGi : Integrable G (ρ.prod μ) := hKD.congr hae
  have hGint : ∫ p, G p ∂(ρ.prod μ) = ∫ x, E x ∂μ := by
    rw [← integral_congr_ae hae, hKDint, hK, integral_prod_mul (fun t => ((χ t : ℝ) : ℂ)) E, integral_complex_ofReal]
    have : ∫ t in Ioi (0 : ℝ), χ t = 1 := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun t ht => hχ0 t (not_lt.mp ht))]
      exact hχ1
    rw [this]; simp

  have hR : ρ.prod μ = (volume.prod μ).restrict (Ioi (0 : ℝ) ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hz : ∀ p : ℝ × (Mt k r × Mt k r), p ∉ Ioi (0 : ℝ) ×ˢ (univ : Set (Mt k r × Mt k r)) → G p = 0 := by
    intro p hp
    have : p.1 ≤ 0 := by
      by_contra hc
      exact hp ⟨not_le.mp hc, mem_univ _⟩
    simp [hG, hχ0 p.1 this]
  have hGv : Integrable G (volume.prod μ) := by
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 (hR ▸ hGi)
    intro p hp
    by_contra hc
    exact hp (hz p hc)
  have hGvint : ∫ p, G p ∂(volume.prod μ) = ∫ p, G p ∂(ρ.prod μ) := by
    rw [hR, setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hF : Integrable (fun z : (Mt k r × Mt k r) × ℝ => G z.swap) (μ.prod volume) := hGv.swap
  calc ∫ x, (∫ t : ℝ, ((χ t * t ^ kap k r : ℝ) : ℂ) * B (x.1, conjM (aDil k r t) x.2) *
        Complex.exp (Complex.I * ((Λ x.2 * t : ℝ) : ℂ))) ∂μ
      = ∫ z, G z.swap ∂(μ.prod volume) := (integral_prod (fun z => G z.swap) hF).symm
    _ = ∫ p, G p ∂(volume.prod μ) := integral_prod_swap G
    _ = ∫ x, E x ∂μ := by rw [hGvint, hGint]

/- English proof (translation)
Establish `e : (Function.uncurry fun (h n : Mt k r) => conjM (Matrix.of h)⁻¹ n) = mul3 ∘ (fun p : Mt k r × Mt k r => (invT p.1, p.2, invT (invT p.1)))`. Use function extensionality and compare the values at `p`. Simplify using `only [Function.comp, Function.uncurry, mul3, invT, conjM]`. Both sides reduce to the same expression. Establish `hmeas : Measurable (Function.uncurry fun (h n : Mt k r) => conjM (Matrix.of h)⁻¹ n)`.

Rewrite using `[e]`. Conclude with `measurable_triple_product.comp ((lim_measurable_inv.comp measurable_fst).prodMk (measurable_snd.prodMk (lim_measurable_inv.comp (lim_measurable_inv.comp measurable_fst))))`. Establish `hmp : MeasurePreserving (fun x : Mt k r × Mt k r => (id x.1, conjM (Matrix.of x.1)⁻¹ x.2)) (μW.prod μN) (μW.prod μN)` using `MeasurePreserving.skew_product (MeasurePreserving.id μW) hmeas (hW.mono fun h hh => hC h hh)`. Establish `hi : Integrable (f ∘ fun x : Mt k r × Mt k r => (id x.1, conjM (Matrix.of x.1)⁻¹ x.2)) (μW.prod μN)` using `(hmp.integrable_comp hf.aestronglyMeasurable).2 hf`. Use `⟨hi.congr hfg, ?_⟩` and prove the remaining obligations.

Rewrite using `[← integral_congr_ae hfg]`. Use `integral_map hmp.measurable.aemeasurable (hmp.map_eq.symm ▸ hf.aestronglyMeasurable)` as an intermediate fact. Rewrite `this` using `[hmp.map_eq]`. Conclude with `this.symm`.
-/
theorem lim_conj_transfer (μW μN : Measure (Mt k r)) [SigmaFinite μW] [SigmaFinite μN] (U : Set (Mat k r))
    (hW : ∀ᵐ h ∂μW, Matrix.of h ∈ U) (hC : ∀ h : Mt k r, Matrix.of h ∈ U → μN.map (conjM (Matrix.of h)⁻¹) = μN)
    (f g : Mt k r × Mt k r → ℂ) (hf : Integrable f (μW.prod μN))
    (hfg : ∀ᵐ x ∂(μW.prod μN), f (x.1, conjM (Matrix.of x.1)⁻¹ x.2) = g x) :
    Integrable g (μW.prod μN) ∧ ∫ x, g x ∂(μW.prod μN) = ∫ x, f x ∂(μW.prod μN) := by
  have e : (Function.uncurry fun (h n : Mt k r) => conjM (Matrix.of h)⁻¹ n) =
      mul3 ∘ (fun p : Mt k r × Mt k r => (invT p.1, p.2, invT (invT p.1))) := by
    funext p
    simp only [Function.comp, Function.uncurry, mul3, invT, conjM]
    rfl
  have hmeas : Measurable (Function.uncurry fun (h n : Mt k r) => conjM (Matrix.of h)⁻¹ n) := by
    rw [e]
    exact measurable_triple_product.comp ((lim_measurable_inv.comp measurable_fst).prodMk
      (measurable_snd.prodMk (lim_measurable_inv.comp (lim_measurable_inv.comp measurable_fst))))
  have hmp : MeasurePreserving (fun x : Mt k r × Mt k r => (id x.1, conjM (Matrix.of x.1)⁻¹ x.2))
      (μW.prod μN) (μW.prod μN) :=
    MeasurePreserving.skew_product (MeasurePreserving.id μW) hmeas (hW.mono fun h hh => hC h hh)
  have hi : Integrable (f ∘ fun x : Mt k r × Mt k r => (id x.1, conjM (Matrix.of x.1)⁻¹ x.2)) (μW.prod μN) :=
    (hmp.integrable_comp hf.aestronglyMeasurable).2 hf
  refine ⟨hi.congr hfg, ?_⟩
  rw [← integral_congr_ae hfg]
  have := integral_map hmp.measurable.aemeasurable (hmp.map_eq.symm ▸ hf.aestronglyMeasurable)
  rw [hmp.map_eq] at this
  exact this.symm

end PI.BICNZ
