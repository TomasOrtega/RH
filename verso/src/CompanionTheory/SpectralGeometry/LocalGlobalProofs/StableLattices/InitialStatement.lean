import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagLocalSizesUnitary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.RgStart

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S ReciprocityTheory.ChartRestriction.DS GlobalTheory.FlagMeas Formalism.MainNotions.S GlobalTheory.Count

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Unfold `modA`. Establish `h1 : Measurable fun τ : Fin 1 → ℝ => layerProd n 1 (fun _ : Fin 1 => rk A) τ id`. Unfold `layerProd`. Simplify using `only [id]`. Use `fun_prop`.

Conclude with `(h1.comp (measurable_pi_lambda _ fun i => measurable_locSize_uMat n ε 1 (fun _ : Fin 1 => rk A) (W A) i)).ennreal_ofReal`.
-/
theorem measurable_modA (A : Matrix (Fin n) (Fin n) ℂ) : Measurable (modA (ε := ε) A) := by
  unfold modA
  have h1 : Measurable fun τ : Fin 1 → ℝ => layerProd n 1 (fun _ : Fin 1 => rk A) τ id := by
    unfold layerProd
    simp only [id]
    fun_prop
  exact (h1.comp (measurable_pi_lambda _ fun i =>
    measurable_locSize_uMat n ε 1 (fun _ : Fin 1 => rk A) (W A) i)).ennreal_ofReal

/- English proof (translation)
Establish `h : ∀ y ∈ V, Matrix.toLin' f y ∈ V` using `fun y hy => by`. Rewrite using `[Matrix.toLin'_apply]`. Conclude with `hV y hy`. Unfold `detOn`. Rewrite using `[dif_pos h]`.

Use `norm_pos_iff.mpr fun h0 => ?_` and prove the remaining obligations. Take `⟨x, hx, hx0⟩` from `SetLike.exists_of_lt (LinearMap.bot_lt_ker_of_det_eq_zero h0)`. Establish `h1 : f *ᵥ (x : Fin n → ℂ) = 0`. Use `congrArg Subtype.val (LinearMap.mem_ker.mp hx)` as an intermediate fact. Simplify `this` using `[Matrix.toLin'_apply]`.

Establish `h2 : (x : Fin n → ℂ) = 0`. Use `congrArg (g *ᵥ ·) h1` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, hgf]`. Conclude with `hx0 (by simpa using Subtype.ext h2)`.
-/
theorem detOn_pos_of_left_inv {f g : Matrix (Fin n) (Fin n) ℂ} (hgf : g * f = 1) (V : Submodule ℂ (Fin n → ℂ))
    (hV : ∀ y ∈ V, f *ᵥ y ∈ V) : 0 < detOn f V := by
  classical
  have h : ∀ y ∈ V, Matrix.toLin' f y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply]
    exact hV y hy
  unfold detOn
  rw [dif_pos h]
  refine norm_pos_iff.mpr fun h0 => ?_
  obtain ⟨x, hx, hx0⟩ := SetLike.exists_of_lt (LinearMap.bot_lt_ker_of_det_eq_zero h0)
  have h1 : f *ᵥ (x : Fin n → ℂ) = 0 := by
    have := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    simpa [Matrix.toLin'_apply] using this
  have h2 : (x : Fin n → ℂ) = 0 := by
    have := congrArg (g *ᵥ ·) h1
    simpa [Matrix.mulVec_mulVec, hgf] using this
  exact hx0 (by simpa using Subtype.ext h2)

/- English proof (translation)
Establish `hinv : (((m : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * uMat m = 1` using `Units.inv_mul _`. Establish `hd : ∀ i, 0 < detOn (uMat m) (W A i)` using `fun i => detOn_pos_of_left_inv hinv _ fun y hy => (hm i y hy).1`. Establish `hτ : ∀ i : Fin 1, 0 < locSize (fun _ : Fin 1 => rk A) (W A) (uMat m) i` using `fun i => Real.rpow_pos_of_pos (div_pos (hd _) (hd _)) _`. Establish `hp : 0 < layerProd n 1 (fun _ : Fin 1 => rk A) (locSize (fun _ : Fin 1 => rk A) (W A) (uMat m)) id`. Unfold `layerProd`.

Simplify using `only [id]`. Conclude with `mul_pos (prod_pos fun i _ => prod_pos fun k _ => mul_pos (pow_pos (div_pos (hτ i) (hτ k)) _) (pow_pos (mul_pos (hτ i) (hτ k)) _)) (prod_pos fun i _ => mul_pos (pow_pos (hτ i) _) (pow_pos (pow_pos (hτ i) _) _))`. Unfold `modA`. Conclude with `(ENNReal.ofReal_pos.mpr hp).ne'`.
-/
theorem modA_ne_zero (A : Matrix (Fin n) (Fin n) ℂ) {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) :
    modA A m ≠ 0 := by
  have hinv : (((m : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      uMat m = 1 := Units.inv_mul _
  have hd : ∀ i, 0 < detOn (uMat m) (W A i) := fun i =>
    detOn_pos_of_left_inv hinv _ fun y hy => (hm i y hy).1
  have hτ : ∀ i : Fin 1, 0 < locSize (fun _ : Fin 1 => rk A) (W A) (uMat m) i := fun i =>
    Real.rpow_pos_of_pos (div_pos (hd _) (hd _)) _
  have hp : 0 < layerProd n 1 (fun _ : Fin 1 => rk A) (locSize (fun _ : Fin 1 => rk A) (W A) (uMat m)) id := by
    unfold layerProd
    simp only [id]
    exact mul_pos (prod_pos fun i _ => prod_pos fun k _ =>
        mul_pos (pow_pos (div_pos (hτ i) (hτ k)) _) (pow_pos (mul_pos (hτ i) (hτ k)) _))
      (prod_pos fun i _ => mul_pos (pow_pos (hτ i) _) (pow_pos (pow_pos (hτ i) _) _))
  unfold modA
  exact (ENNReal.ofReal_pos.mpr hp).ne'

/- English proof (translation)
Introduce `_ _ hLine hSlab hFub hKMaj n ε H _ _ _ σ D E hK hU hL2 A μ hA hμ u ξ`. Take `⟨F, hFm, hFK, hFint, hFle⟩` from `hKMaj n ε H σ D E hK hU hL2 u ξ`. Take `⟨μN, μM, hN, hM, hMS, hMinv, ⟨κ, hκ0, hκt, hκ⟩, hnull⟩` from `hFub n ε A hA`. Take `⟨a, τ, ha, hτ, haM, hadd, haS, hcent, hmod, htime⟩` from `hLine n ε A hA`. Use `haveI := hN`.

Use `haveI := hM`. Take `⟨⟨Msub, eM⟩, hS, -⟩` from `GlobalTheory.FlagLeviGroup.levi_compact_subgroups n ε 1 (W A)`. Establish `hfin : (∫⁻ v, ∫⁻ m, modA A m * F (v * m) ∂μM ∂μN) < ⊤`. Establish `h` using `hFint`. Rewrite `h` using `[hκ F hFm hFK]`.

Conclude with `ENNReal.lt_top_of_mul_ne_top_right h.ne hκ0`. Establish `h1N : (1 : Formalism.REAL.UJ ε) ∈ flagN ε (W A)`. Apply the tactic sequence `refine ⟨fun i y _ => ?_, fun y _ => ?_⟩ <;>`. Rewrite using `[GlobalTheory.FlagLeviGroup.uMat_one, Matrix.one_mulVec, sub_self]`. Conclude with `Submodule.zero_mem _`.

Establish `hsl` using `hSlab (Formalism.REAL.UJ ε) μN μM (flagM ε (W A)) a (modA A) τ (rhoA A) hS.measurableSet hMS ha.measurable (measurable_modA A) hτ hadd (fun m hm t => by`. Establish `: m * a t ∈ Msub` using `Msub.mul_mem (by rw [← SetLike.mem_coe, eM]; exact hm) (by rw [← SetLike.mem_coe, eM]; exact haS t)`. Rewrite using `[← eM]`. Conclude with `this)`. Use the proof step `(fun t => hMinv (a t) (haS t) (hcent t)) hmod`.

Use the proof step `(fun m hm t => by simpa using htime 1 h1N m hm t)`. Use the proof step `(fun m hm => modA_ne_zero A hm) F hFm hfin`. Set `I : Formalism.REAL.UJ ε → ℝ≥0∞` to `fun x => ∫⁻ t in Set.Ioi (0 : ℝ), F (x * a t) * ENNReal.ofReal (Real.exp (2 * rhoA A * t))`. Establish `hI : Measurable I` using `Measurable.lintegral_prod_right' (f := fun p : Formalism.REAL.UJ ε × ℝ => F (p.1 * a p.2) * ENNReal.ofReal (Real.exp (2 * rhoA A * p.2))) ((hFm.comp (measurable_fst.mul (ha.measurable.comp measurable_snd))).mul (by fun_prop))`. Establish `hE : MeasurableSet (I ⁻¹' {⊤})` using `hI (measurableSet_singleton ⊤)`.

Establish `h0 : (μN.prod μM) {p | p.1 * p.2 ∈ I ⁻¹' {⊤}} = 0`. Use `measure_mono_null (fun p hp => ?_) (ae_iff.mp hsl)` and prove the remaining obligations. Establish `hp' : I (p.1 * p.2) = ⊤` using `hp`. Use `show ¬ I (p.1 * p.2) < ⊤`. Rewrite using `[hp']`.

Conclude with `lt_irrefl _`. Establish `hμE : μ (I ⁻¹' {⊤}) = 0` using `hnull μ hμ _ hE h0`. Establish `hae : ∀ᵐ x ∂μ, I x ≠ ⊤`. Use `ae_iff.mpr (measure_mono_null (fun x hx => ?_) hμE)` and prove the remaining obligations. Conclude with `not_not.mp hx`.

Establish `hle : ∀ y : Formalism.REAL.UJ ε, lineInt ε (baseCoef σ D ξ u) A (-rhoA A) y ≤ I y`. Introduce `y`. Unfold `lineInt`. Use `lintegral_mono fun t => ?_` and prove the remaining obligations. Establish `e1 : S7.toM y * NormedSpace.exp ((t : ℂ) • A) = uMat (y * a t)`.

Rewrite using `[← haM t]`. Both sides reduce to the same expression. Establish `e2 : Real.exp (-2 * (-rhoA A) * t) = Real.exp (2 * rhoA A * t)`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, e2]`. Conclude with `mul_le_mul' (hFle _) le_rfl`. Use `filter_upwards [hae] with x hx`. Conclude with `lt_of_le_of_lt (hle x) (lt_top_iff_ne_top.mpr hx)`.
-/
theorem startOf : StartOf := by
  intro _ _ hLine hSlab hFub hKMaj n ε H _ _ _ σ D E hK hU hL2 A μ hA hμ u ξ
  obtain ⟨F, hFm, hFK, hFint, hFle⟩ := hKMaj n ε H σ D E hK hU hL2 u ξ
  obtain ⟨μN, μM, hN, hM, hMS, hMinv, ⟨κ, hκ0, hκt, hκ⟩, hnull⟩ := hFub n ε A hA
  obtain ⟨a, τ, ha, hτ, haM, hadd, haS, hcent, hmod, htime⟩ := hLine n ε A hA
  haveI := hN
  haveI := hM
  obtain ⟨⟨Msub, eM⟩, hS, -⟩ := GlobalTheory.FlagLeviGroup.levi_compact_subgroups n ε 1 (W A)
  have hfin : (∫⁻ v, ∫⁻ m, modA A m * F (v * m) ∂μM ∂μN) < ⊤ := by
    have h := hFint
    rw [hκ F hFm hFK] at h
    exact ENNReal.lt_top_of_mul_ne_top_right h.ne hκ0
  have h1N : (1 : Formalism.REAL.UJ ε) ∈ flagN ε (W A) := by
    refine ⟨fun i y _ => ?_, fun y _ => ?_⟩ <;>
      · rw [GlobalTheory.FlagLeviGroup.uMat_one, Matrix.one_mulVec, sub_self]
        exact Submodule.zero_mem _
  have hsl := hSlab (Formalism.REAL.UJ ε) μN μM (flagM ε (W A)) a (modA A) τ (rhoA A) hS.measurableSet hMS ha.measurable
    (measurable_modA A) hτ hadd
    (fun m hm t => by
      have : m * a t ∈ Msub := Msub.mul_mem (by rw [← SetLike.mem_coe, eM]; exact hm)
        (by rw [← SetLike.mem_coe, eM]; exact haS t)
      rw [← eM]; exact this)
    (fun t => hMinv (a t) (haS t) (hcent t)) hmod
    (fun m hm t => by simpa using htime 1 h1N m hm t)
    (fun m hm => modA_ne_zero A hm) F hFm hfin
  let I : Formalism.REAL.UJ ε → ℝ≥0∞ := fun x =>
    ∫⁻ t in Set.Ioi (0 : ℝ), F (x * a t) * ENNReal.ofReal (Real.exp (2 * rhoA A * t))
  have hI : Measurable I := Measurable.lintegral_prod_right'
    (f := fun p : Formalism.REAL.UJ ε × ℝ => F (p.1 * a p.2) * ENNReal.ofReal (Real.exp (2 * rhoA A * p.2)))
    ((hFm.comp (measurable_fst.mul (ha.measurable.comp measurable_snd))).mul (by fun_prop))
  have hE : MeasurableSet (I ⁻¹' {⊤}) := hI (measurableSet_singleton ⊤)
  have h0 : (μN.prod μM) {p | p.1 * p.2 ∈ I ⁻¹' {⊤}} = 0 := by
    refine measure_mono_null (fun p hp => ?_) (ae_iff.mp hsl)
    have hp' : I (p.1 * p.2) = ⊤ := hp
    show ¬ I (p.1 * p.2) < ⊤
    rw [hp']
    exact lt_irrefl _
  have hμE : μ (I ⁻¹' {⊤}) = 0 := hnull μ hμ _ hE h0
  have hae : ∀ᵐ x ∂μ, I x ≠ ⊤ := by
    refine ae_iff.mpr (measure_mono_null (fun x hx => ?_) hμE)
    exact not_not.mp hx
  have hle : ∀ y : Formalism.REAL.UJ ε, lineInt ε (baseCoef σ D ξ u) A (-rhoA A) y ≤ I y := by
    intro y
    unfold lineInt
    refine lintegral_mono fun t => ?_
    have e1 : S7.toM y * NormedSpace.exp ((t : ℂ) • A) = uMat (y * a t) := by
      rw [← haM t]
      rfl
    have e2 : Real.exp (-2 * (-rhoA A) * t) = Real.exp (2 * rhoA A * t) := by
      congr 1
      ring
    rw [e1, e2]
    exact mul_le_mul' (hFle _) le_rfl
  filter_upwards [hae] with x hx
  exact lt_of_le_of_lt (hle x) (lt_top_iff_ne_top.mpr hx)

end GlobalTheory.CompanionTheory.RgStart
