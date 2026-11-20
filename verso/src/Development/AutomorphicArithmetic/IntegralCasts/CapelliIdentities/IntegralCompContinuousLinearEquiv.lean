import Mathlib

noncomputable def UpperTheory.Reformulated.B.Yzb9.SelfDual :
    {V : Type} →
      [AddCommGroup V] → [TopologicalSpace V] → [inst : MeasurableSpace V] → MeasureTheory.Measure V → (V → V → ℂ) → Prop :=
    fun {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (μ : MeasureTheory.Measure V) (χ : V → V → ℂ) ↦
      μ.IsAddHaarMeasure ∧
        ∀ (Φ : V → ℂ),
          Continuous Φ →
            HasCompactSupport Φ →
              MeasureTheory.Integrable (fun (y : V) ↦ ∫ (x : V), Φ x * χ x y ∂μ) μ →
                ∀ (z : V), ∫ (y : V), (∫ (x : V), Φ x * χ x y ∂μ) * χ y z ∂μ = Φ (-z)

section
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/- English proof (translation)
Establish `hd : LinearMap.det (T.toLinearEquiv : E →ₗ[ℝ] E) ≠ 0` using `(LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero`. Conclude with `Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd`.
-/
private lemma UpperTheory.Reformulated.B.Yzb9.map_T (T : E ≃L[ℝ] E) :
    Measure.map T (volume : Measure E) =
      ENNReal.ofReal |(LinearMap.det (T.toLinearEquiv : E →ₗ[ℝ] E))⁻¹| • (volume : Measure E) := by
  have hd : LinearMap.det (T.toLinearEquiv : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero
  exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd

/- English proof (translation)
Establish `hd : LinearMap.det (T.toLinearEquiv : E →ₗ[ℝ] E) ≠ 0` using `(LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero`. Establish `h1` using `T.toHomeomorph.measurableEmbedding.integrable_map_iff (μ := (volume : Measure E)) (g := g)`. Establish `hk : ENNReal.ofReal |(LinearMap.det (T.toLinearEquiv : E →ₗ[ℝ] E))⁻¹| ≠ 0`. Simplify using `[hd]`. Establish `h2` using `map_T T`.

Express the relevant statement in the definitionally equal form `Integrable g (Measure.map T volume) ↔ Integrable (g ∘ T) volume at h1`. Rewrite `h1` using `[h2, integrable_smul_measure hk ENNReal.ofReal_ne_top]`. Conclude with `h1.symm`.
-/
private lemma UpperTheory.Reformulated.B.Yzb9.integrable_comp_continuousLinearEquiv_iff (T : E ≃L[ℝ] E) (g : E → ℂ) :
    Integrable (fun v => g (T v)) ↔ Integrable g := by
  have hd : LinearMap.det (T.toLinearEquiv : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero
  have h1 := T.toHomeomorph.measurableEmbedding.integrable_map_iff (μ := (volume : Measure E)) (g := g)
  have hk : ENNReal.ofReal |(LinearMap.det (T.toLinearEquiv : E →ₗ[ℝ] E))⁻¹| ≠ 0 := by
    simp [hd]
  have h2 := map_T T
  change Integrable g (Measure.map T volume) ↔ Integrable (g ∘ T) volume at h1
  rw [h2, integrable_smul_measure hk ENNReal.ofReal_ne_top] at h1
  exact h1.symm

/- English proof (translation)
Establish `h1` using `T.toHomeomorph.measurableEmbedding.integral_map (μ := (volume : Measure E)) g`. Express the relevant statement in the definitionally equal form `∫ y, g y ∂(Measure.map T volume) = ∫ x, g (T x) at h1`. Rewrite using `[← h1, map_T T, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]`.
-/
private lemma UpperTheory.Reformulated.B.Yzb9.integral_comp_continuousLinearEquiv (T : E ≃L[ℝ] E) (g : E → ℂ) :
    ∫ v, g (T v) = (|(LinearMap.det (T.toLinearEquiv : E →ₗ[ℝ] E))⁻¹| : ℝ) • ∫ s, g s := by
  have h1 := T.toHomeomorph.measurableEmbedding.integral_map (μ := (volume : Measure E)) g
  change ∫ y, g y ∂(Measure.map T volume) = ∫ x, g (T x) at h1
  rw [← h1, map_T T, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]

/- English proof (translation)
Rewrite using `[Real.fourierInv_eq']`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Rewrite using `[mul_comm]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma UpperTheory.Reformulated.B.Yzb9.fourierInv_apply (Φ : E → ℂ) (w : E) :
    𝓕⁻ Φ w = ∫ u, Φ u * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪u, w⟫) : ℂ)) := by
  rw [Real.fourierInv_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/- English proof (translation)
Establish `h0 : ∀ v, (𝓕⁻ Φ (T v)) * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪v, T w⟫) : ℂ)) = (fun s => 𝓕⁻ Φ s * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪s, w⟫) : ℂ))) (T v)`. Introduce `v`. Simplify using `only [hT]`. Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall h0), integral_comp_continuousLinearEquiv T (fun s => 𝓕⁻ Φ s * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪s, w⟫) : ℂ))), ← fourierInv_apply]`. Use `congr 1`.

Establish `hF : Integrable (𝓕 Φ)`. Establish `: 𝓕 Φ = fun v => 𝓕⁻ Φ (-v)`. Use extensionality with `v`. Rewrite using `[Real.fourierInv_eq_fourier_neg, neg_neg]`. Rewrite using `[this]`.

Conclude with `hG.comp_neg`. Use `hc.fourier_fourierInv_eq hi hF` as an intermediate fact. Rewrite using `[Real.fourierInv_eq_fourier_neg, this]`.
-/
private lemma UpperTheory.Reformulated.B.Yzb9.core (T : E ≃L[ℝ] E) (hT : ∀ u v, ⟪u, T v⟫ = ⟪T u, v⟫)
    (Φ : E → ℂ) (hc : Continuous Φ) (hi : Integrable Φ)
    (hG : Integrable (𝓕⁻ Φ)) (w : E) :
    ∫ v, (𝓕⁻ Φ (T v)) * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪v, T w⟫) : ℂ)) =
      (|(LinearMap.det (T.toLinearEquiv : E →ₗ[ℝ] E))⁻¹| : ℝ) • Φ (-w) := by
  have h0 : ∀ v, (𝓕⁻ Φ (T v)) * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪v, T w⟫) : ℂ))
      = (fun s => 𝓕⁻ Φ s * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪s, w⟫) : ℂ))) (T v) := by
    intro v
    simp only [hT]
  rw [integral_congr_ae (Filter.Eventually.of_forall h0),
    integral_comp_continuousLinearEquiv T (fun s => 𝓕⁻ Φ s * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪s, w⟫) : ℂ))),
    ← fourierInv_apply]
  congr 1
  have hF : Integrable (𝓕 Φ) := by
    have : 𝓕 Φ = fun v => 𝓕⁻ Φ (-v) := by
      ext v
      rw [Real.fourierInv_eq_fourier_neg, neg_neg]
    rw [this]
    exact hG.comp_neg
  have := hc.fourier_fourierInv_eq hi hF
  rw [Real.fourierInv_eq_fourier_neg, this]
end

section
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace NNReal

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/- English proof (translation)
Rewrite using `[integral_smul_nnreal_measure, fourierInv_apply]`. Both sides reduce to the same expression.
-/
private lemma UpperTheory.Reformulated.B.Yzb9.inner_eq (T : E ≃L[ℝ] E) (c : ℝ≥0) (Φ : E → ℂ) (y : E) :
    ∫ x, Φ x * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪x, T y⟫) : ℂ)) ∂(c • (volume : Measure E)) = (c : ℝ) • 𝓕⁻ Φ (T y) := by
  rw [integral_smul_nnreal_measure, fourierInv_apply]
  rfl

/- English proof (translation)
Rewrite using `[funext (inner_eq T c Φ)]`. Establish `hcE : (c : ENNReal) ≠ 0` using `by simpa using hc`. Establish `hm : c • (volume : Measure E) = (c : ENNReal) • (volume : Measure E)` using `rfl`. Rewrite using `[hm, integrable_smul_measure hcE ENNReal.coe_ne_top, ← integrable_comp_continuousLinearEquiv_iff T (𝓕⁻ Φ)]`. Establish `hc' : (c : ℝ) ≠ 0` using `by simpa using hc`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `h.smul ((c : ℝ)⁻¹)` as an intermediate fact. Establish `h2 : ((c : ℝ)⁻¹ • fun y => (c : ℝ) • 𝓕⁻ Φ (T y)) = fun y => 𝓕⁻ Φ (T y)`. Use function extensionality and compare the values at `y`.

Simplify using `[smul_smul, hc']`. Rewrite `this` using `[h2]`. Then use the resulting hypothesis. Introduce `h`. Conclude with `h.smul (c : ℝ)`.
-/
private lemma UpperTheory.Reformulated.B.Yzb9.integrable_iff (T : E ≃L[ℝ] E) (c : ℝ≥0) (hc : c ≠ 0) (Φ : E → ℂ) :
    Integrable (fun y => ∫ x, Φ x * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪x, T y⟫) : ℂ)) ∂(c • (volume : Measure E)))
      (c • (volume : Measure E)) ↔ Integrable (𝓕⁻ Φ) := by
  rw [funext (inner_eq T c Φ)]
  have hcE : (c : ENNReal) ≠ 0 := by simpa using hc
  have hm : c • (volume : Measure E) = (c : ENNReal) • (volume : Measure E) := rfl
  rw [hm, integrable_smul_measure hcE ENNReal.coe_ne_top, ← integrable_comp_continuousLinearEquiv_iff T (𝓕⁻ Φ)]
  have hc' : (c : ℝ) ≠ 0 := by simpa using hc
  constructor
  · intro h
    have := h.smul ((c : ℝ)⁻¹)
    have h2 : ((c : ℝ)⁻¹ • fun y => (c : ℝ) • 𝓕⁻ Φ (T y)) = fun y => 𝓕⁻ Φ (T y) := by
      funext y
      simp [smul_smul, hc']
    rwa [h2] at this
  · intro h
    exact h.smul (c : ℝ)

/- English proof (translation)
Establish `h0 : ∀ y, (∫ x, Φ x * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪x, T y⟫) : ℂ)) ∂(c • (volume : Measure E))) * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪y, T z⟫) : ℂ)) = (c : ℝ) • (𝓕⁻ Φ (T y) * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪y, …`. Introduce `y`. Rewrite using `[inner_eq, smul_mul_assoc]`. Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall h0), integral_smul_nnreal_measure, integral_smul, core T hT Φ hc (hc.integrable_of_hasCompactSupport hs) hG z]`. Simplify using `only [NNReal.smul_def, smul_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma UpperTheory.Reformulated.B.Yzb9.key (T : E ≃L[ℝ] E) (hT : ∀ u v, ⟪u, T v⟫ = ⟪T u, v⟫) (c : ℝ≥0)
    (Φ : E → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ) (hG : Integrable (𝓕⁻ Φ)) (z : E) :
    ∫ y, (∫ x, Φ x * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪x, T y⟫) : ℂ)) ∂(c • (volume : Measure E))) * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪y, T z⟫) : ℂ))
        ∂(c • (volume : Measure E)) = ((c : ℝ) ^ 2 * |(LinearMap.det (T.toLinearEquiv : E →ₗ[ℝ] E))⁻¹|) • Φ (-z) := by
  have h0 : ∀ y, (∫ x, Φ x * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪x, T y⟫) : ℂ)) ∂(c • (volume : Measure E))) * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪y, T z⟫) : ℂ)) =
      (c : ℝ) • (𝓕⁻ Φ (T y) * Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪y, T z⟫) : ℂ))) := by
    intro y
    rw [inner_eq, smul_mul_assoc]
  rw [integral_congr_ae (Filter.Eventually.of_forall h0), integral_smul_nnreal_measure,
    integral_smul, core T hT Φ hc (hc.integrable_of_hasCompactSupport hs) hG z]
  simp only [NNReal.smul_def, smul_smul]
  congr 1
  ring

/- English proof (translation)
Set `b : ContDiffBump (0 : E)` to `⟨1, 2, one_pos, one_lt_two⟩`. Establish `h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ))` using `b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)`. Establish `h2 : ContDiff ℝ (⊤ : ENat) (fun x => ((b x : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp b.contDiff`. Use `⟨fun x => ((b x : ℝ) : ℂ), ?_, h1, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Complex.continuous_ofReal.comp b.continuous`.

Establish `: b 0 = 1` using `b.one_of_mem_closedBall (by simp [b.rIn_pos.le])`. Simplify using `[this]`. Set `S : SchwartzMap E ℂ` to `h1.toSchwartzMap h2`. Establish `: 𝓕⁻ (fun x => ((b x : ℝ) : ℂ)) = ((𝓕⁻ S : SchwartzMap E ℂ) : E → ℂ)`. Rewrite using `[SchwartzMap.fourierInv_coe]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `(𝓕⁻ S : SchwartzMap E ℂ).integrable`.
-/
private lemma UpperTheory.Reformulated.B.Yzb9.test_fun :
    ∃ Φ : E → ℂ, Continuous Φ ∧ HasCompactSupport Φ ∧ Φ 0 ≠ 0 ∧ Integrable (𝓕⁻ Φ) := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have h2 : ContDiff ℝ (⊤ : ENat) (fun x => ((b x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨fun x => ((b x : ℝ) : ℂ), ?_, h1, ?_, ?_⟩
  · exact Complex.continuous_ofReal.comp b.continuous
  · have : b 0 = 1 := b.one_of_mem_closedBall (by simp [b.rIn_pos.le])
    simp [this]
  · let S : SchwartzMap E ℂ := h1.toSchwartzMap h2
    have : 𝓕⁻ (fun x => ((b x : ℝ) : ℂ)) = ((𝓕⁻ S : SchwartzMap E ℂ) : E → ℂ) := by
      rw [SchwartzMap.fourierInv_coe]
      rfl
    rw [this]
    exact (𝓕⁻ S : SchwartzMap E ℂ).integrable

/- English proof (translation)
Establish `hd : LinearMap.det (T.toLinearEquiv : E →ₗ[ℝ] E) ≠ 0` using `(LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero`. Use `set D : ℝ := |(LinearMap.det (T.toLinearEquiv : E →ₗ[ℝ] E))⁻¹| with hD`. Establish `hDpos : 0 < D` using `abs_pos.mpr (inv_ne_zero hd)`. Set `c : ℝ≥0` to `⟨√(D⁻¹), Real.sqrt_nonneg _⟩`. Establish `hc2 : (c : ℝ) ^ 2 * D = 1`.

Express the relevant statement in the definitionally equal form `(√(D⁻¹)) ^ 2 * D = 1`. Rewrite using `[Real.sq_sqrt (inv_pos.mpr hDpos).le, inv_mul_cancel₀ hDpos.ne']`. Establish `hc0 : c ≠ 0`. Introduce and unpack `h`. Rewrite `hc2` using `[h]`.

Simplify using `at hc2`. Use `⟨c • (volume : Measure E), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hcE : (c : ENNReal) ≠ 0` using `by simpa using hc0`. Conclude with `Measure.IsAddHaarMeasure.smul _ hcE ENNReal.coe_ne_top`. Introduce `Φ hΦ hs hi z`.

Establish `hG` using `(integrable_iff T c hc0 Φ).mp hi`. Use `key T hT c Φ hΦ hs hG z` as an intermediate fact. Rewrite `this` using `[hc2, one_smul]`. Conclude with `this`. Introduce and unpack `m' ⟨hH, hS⟩`.

Establish `hm : m' = Measure.addHaarScalarFactor m' volume • (volume : Measure E)` using `Measure.isAddLeftInvariant_eq_smul m' volume`. Establish `hpos` using `Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure m' (volume : Measure E)`. Use `set c' : ℝ≥0 := Measure.addHaarScalarFactor m' volume with hc'`. Take `⟨Φ, hΦ, hs, h0, hG⟩` from `test_fun (E := E)`. Rewrite `hS` using `[hm]`.

Establish `h1` using `hS Φ hΦ hs ((integrable_iff T c' hpos.ne' Φ).mpr hG) 0`. Rewrite `h1` using `[key T hT c' Φ hΦ hs hG 0, neg_zero]`. Establish `h2 : (c' : ℝ) ^ 2 * D = 1`. Establish `h3 : (((c' : ℝ) ^ 2 * D : ℝ) : ℂ) * Φ 0 = 1 * Φ 0`. Rewrite using `[one_mul]`.

Conclude with `h1`. Use `mul_right_cancel₀ h0 h3` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `h4 : (c' : ℝ) = c`. Establish `h5 : (c' : ℝ) ^ 2 = (c : ℝ) ^ 2` using `mul_right_cancel₀ hDpos.ne' (h2.trans hc2.symm)`.

Conclude with `(pow_left_inj₀ c'.2 c.2 two_ne_zero).mp h5`. Establish `h6 : c' = c` using `NNReal.coe_injective h4`. Rewrite using `[hm, h6]`.
-/
private lemma UpperTheory.Reformulated.B.Yzb9.existsUnique_E (T : E ≃L[ℝ] E) (hT : ∀ u v, ⟪u, T v⟫ = ⟪T u, v⟫) :
    ∃! m : Measure E, UpperTheory.Reformulated.B.Yzb9.SelfDual m (fun u v => Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(⟪u, T v⟫) : ℂ))) := by
  have hd : LinearMap.det (T.toLinearEquiv : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero
  set D : ℝ := |(LinearMap.det (T.toLinearEquiv : E →ₗ[ℝ] E))⁻¹| with hD
  have hDpos : 0 < D := abs_pos.mpr (inv_ne_zero hd)
  let c : ℝ≥0 := ⟨√(D⁻¹), Real.sqrt_nonneg _⟩
  have hc2 : (c : ℝ) ^ 2 * D = 1 := by
    change (√(D⁻¹)) ^ 2 * D = 1
    rw [Real.sq_sqrt (inv_pos.mpr hDpos).le, inv_mul_cancel₀ hDpos.ne']
  have hc0 : c ≠ 0 := by
    rintro h
    rw [h] at hc2
    simp at hc2
  refine ⟨c • (volume : Measure E), ⟨?_, ?_⟩, ?_⟩
  · have hcE : (c : ENNReal) ≠ 0 := by simpa using hc0
    exact Measure.IsAddHaarMeasure.smul _ hcE ENNReal.coe_ne_top
  · intro Φ hΦ hs hi z
    have hG := (integrable_iff T c hc0 Φ).mp hi
    have := key T hT c Φ hΦ hs hG z
    rw [hc2, one_smul] at this
    exact this
  · rintro m' ⟨hH, hS⟩
    have hm : m' = Measure.addHaarScalarFactor m' volume • (volume : Measure E) :=
      Measure.isAddLeftInvariant_eq_smul m' volume
    have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure m' (volume : Measure E)
    set c' : ℝ≥0 := Measure.addHaarScalarFactor m' volume with hc'
    obtain ⟨Φ, hΦ, hs, h0, hG⟩ := test_fun (E := E)
    rw [hm] at hS
    have h1 := hS Φ hΦ hs ((integrable_iff T c' hpos.ne' Φ).mpr hG) 0
    rw [key T hT c' Φ hΦ hs hG 0, neg_zero] at h1
    have h2 : (c' : ℝ) ^ 2 * D = 1 := by
      have h3 : (((c' : ℝ) ^ 2 * D : ℝ) : ℂ) * Φ 0 = 1 * Φ 0 := by
        rw [one_mul]
        exact h1
      have := mul_right_cancel₀ h0 h3
      exact_mod_cast this
    have h4 : (c' : ℝ) = c := by
      have h5 : (c' : ℝ) ^ 2 = (c : ℝ) ^ 2 := mul_right_cancel₀ hDpos.ne' (h2.trans hc2.symm)
      exact (pow_left_inj₀ c'.2 c.2 two_ne_zero).mp h5
    have h6 : c' = c := NNReal.coe_injective h4
    rw [hm, h6]

/- English proof (translation)
Use `haveI := FiniteDimensional.complete ℝ E`. Set `A : E → (E →L[ℝ] ℝ)` to `fun v => AddMonoidHom.toRealLinearMap (AddMonoidHom.mk' (fun u => p u v) (fun a b => hadd a b v)) (hcont v)`. Establish `hA : ∀ v u, A v u = p u v` using `fun v u => rfl`. Set `T0 : E → E` to `fun v => (InnerProductSpace.toDual ℝ E).symm (A v)`. Establish `hT0 : ∀ u v, ⟪T0 v, u⟫ = p u v`.

Introduce `u v`. Rewrite using `[InnerProductSpace.toDual_symm_apply, hA]`. Set `Tl : E →ₗ[ℝ] E` to `{ toFun := T0 map_add' := by`. Introduce `a b`. Apply `ext_inner_right ℝ` to reduce the goal to its premises.

Introduce `u`. Rewrite using `[inner_add_left, hT0, hT0, hT0, hsym u (a + b), hadd, hsym a, hsym b]`. Use the proof step `map_smul' := by`. Introduce `r a`. Apply `ext_inner_right ℝ` to reduce the goal to its premises.

Introduce `u`. Establish `h1 : p (r • a) u = r * p a u`. Rewrite using `[← hA, ← hA, map_smul, smul_eq_mul]`. Simplify using `only [RingHom.id_apply]`. Rewrite using `[hT0, real_inner_smul_left, hT0, hsym u, hsym u a, h1] }`.

Establish `hTl : ∀ v, Tl v = T0 v` using `fun v => rfl`. Establish `hinj : Function.Injective Tl`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `v hv`. Apply `hnd v` to reduce the goal to its premises.

Introduce `w`. Rewrite using `[hsym, ← hT0, ← hTl, hv, inner_zero_left]`. Use `⟨(LinearEquiv.ofInjectiveEndo Tl hinj).toContinuousLinearEquiv, fun u v => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `p u v = ⟪u, Tl v⟫`. Rewrite using `[hTl, real_inner_comm, hT0]`.
-/
private lemma UpperTheory.Reformulated.B.Yzb9.exists_strictHenselian_absolutely_closed_local_ring (p : E → E → ℝ)
    (hadd : ∀ u u' v, p (u + u') v = p u v + p u' v) (hsym : ∀ u v, p u v = p v u)
    (hcont : ∀ v, Continuous fun u => p u v) (hnd : ∀ u, (∀ v, p u v = 0) → u = 0) :
    ∃ T : E ≃L[ℝ] E, ∀ u v, p u v = ⟪u, T v⟫ := by
  haveI := FiniteDimensional.complete ℝ E
  let A : E → (E →L[ℝ] ℝ) := fun v =>
    AddMonoidHom.toRealLinearMap (AddMonoidHom.mk' (fun u => p u v) (fun a b => hadd a b v)) (hcont v)
  have hA : ∀ v u, A v u = p u v := fun v u => rfl
  let T0 : E → E := fun v => (InnerProductSpace.toDual ℝ E).symm (A v)
  have hT0 : ∀ u v, ⟪T0 v, u⟫ = p u v := by
    intro u v
    rw [InnerProductSpace.toDual_symm_apply, hA]
  let Tl : E →ₗ[ℝ] E :=
    { toFun := T0
      map_add' := by
        intro a b
        apply ext_inner_right ℝ
        intro u
        rw [inner_add_left, hT0, hT0, hT0, hsym u (a + b), hadd, hsym a, hsym b]
      map_smul' := by
        intro r a
        apply ext_inner_right ℝ
        intro u
        have h1 : p (r • a) u = r * p a u := by
          rw [← hA, ← hA, map_smul, smul_eq_mul]
        simp only [RingHom.id_apply]
        rw [hT0, real_inner_smul_left, hT0, hsym u, hsym u a, h1] }
  have hTl : ∀ v, Tl v = T0 v := fun v => rfl
  have hinj : Function.Injective Tl := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    apply hnd v
    intro w
    rw [hsym, ← hT0, ← hTl, hv, inner_zero_left]
  refine ⟨(LinearEquiv.ofInjectiveEndo Tl hinj).toContinuousLinearEquiv, fun u v => ?_⟩
  change p u v = ⟪u, Tl v⟫
  rw [hTl, real_inner_comm, hT0]

/- English proof (translation)
Take `⟨hH, h⟩` from `h`. Set `φ : V ≃ₜ E` to `{ toEquiv := f.toEquiv, continuous_toFun := hf, continuous_invFun := hf' }`. Establish `hme : MeasurableEmbedding f` using `φ.measurableEmbedding`. Use `⟨f.isAddHaarMeasure_map μ hf hf', fun Φ hc hs hi z => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ y, ∫ x, Φ x * χ (f.symm x) (f.symm y) ∂(μ.map f) = ∫ x, Φ (f x) * χ x (f.symm y) ∂μ`.

Introduce `y`. Rewrite using `[hme.integral_map]`. Simplify using the standard rewrite rules. Rewrite `hi`, the goal using `[h1]`. Rewrite using `[hme.integral_map]`.

Establish `hi'` using `hme.integrable_map_iff.mp hi`. Establish `h2` using `h (fun x => Φ (f x)) (hc.comp hf) (hs.comp_homeomorph φ) (by simpa [Function.comp_def] using hi') (f.symm z)`. Simplify using `using h2`.
-/
private lemma UpperTheory.Reformulated.B.Yzb9.selfDual_map {V E : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [MeasurableSpace E] [BorelSpace E]
    (f : V ≃+ E) (hf : Continuous f) (hf' : Continuous f.symm) (μ : Measure V) (χ : V → V → ℂ)
    (h : UpperTheory.Reformulated.B.Yzb9.SelfDual μ χ) :
    UpperTheory.Reformulated.B.Yzb9.SelfDual (μ.map f) (fun u v => χ (f.symm u) (f.symm v)) := by
  obtain ⟨hH, h⟩ := h
  let φ : V ≃ₜ E := { toEquiv := f.toEquiv, continuous_toFun := hf, continuous_invFun := hf' }
  have hme : MeasurableEmbedding f := φ.measurableEmbedding
  refine ⟨f.isAddHaarMeasure_map μ hf hf', fun Φ hc hs hi z => ?_⟩
  have h1 : ∀ y, ∫ x, Φ x * χ (f.symm x) (f.symm y) ∂(μ.map f) =
      ∫ x, Φ (f x) * χ x (f.symm y) ∂μ := by
    intro y
    rw [hme.integral_map]
    simp
  simp_rw [h1] at hi ⊢
  rw [hme.integral_map]
  have hi' := hme.integrable_map_iff.mp hi
  have h2 := h (fun x => Φ (f x)) (hc.comp hf) (hs.comp_homeomorph φ)
    (by simpa [Function.comp_def] using hi') (f.symm z)
  simpa using h2
end

/- English proof (translation)
Introduce `V W _ _ _ _ _ _ _ _ e he he' l hadd hsym hcont hnd`. Set `ψ` to `toEuclidean (E := W)`. Set `f : V ≃+ EuclideanSpace ℝ (Fin (Module.finrank ℝ W))` to `e.trans ψ.toLinearEquiv.toAddEquiv`. Establish `hf : Continuous f` using `ψ.continuous.comp he`. Establish `hf' : Continuous f.symm` using `he'.comp ψ.symm.continuous`.

Take `⟨T, hT⟩` from `UpperTheory.Reformulated.B.Yzb9.exists_strictHenselian_absolutely_closed_local_ring (fun u v => l (f.symm u) (f.symm v)) (fun u u' v => by simp only [map_add, hadd]) (fun u v => hsym _ _) (fun v => (hcont _).comp hf') (fun u hu => by`. Establish `: f.symm u = 0` using `hnd _ (fun y => by`. Use `hu (f y)` as an intermediate fact. Simplify using `using this)`. Simplify using `using this)`.

Establish `hTs : ∀ u v, inner ℝ u (T v) = inner ℝ (T u) v`. Introduce `u v`. Rewrite using `[← hT, hsym, hT, real_inner_comm]`. Take `⟨m, hm, huniq⟩` from `UpperTheory.Reformulated.B.Yzb9.existsUnique_E T hTs`. Establish `hfm : Measurable f` using `hf.measurable`.

Establish `hfm' : Measurable f.symm` using `hf'.measurable`. Use `⟨m.map f.symm, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `UpperTheory.Reformulated.B.Yzb9.selfDual_map f.symm hf' hf m _ hm`. Establish `h2 : (fun (x y : V) => Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(l x y) : ℂ))) = fun x y => Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(inner ℝ (f.symm.symm x) (T (f.symm.symm y))) : ℂ))`. Use function extensionality and compare the values at `x y`.

Rewrite using `[← hT]`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `UpperTheory.Reformulated.B.Yzb9.SelfDual (m.map f.symm) _`. Rewrite using `[h2]`. Conclude with `h1`.

Introduce `μ hμ`. Establish `h1` using `UpperTheory.Reformulated.B.Yzb9.selfDual_map f hf hf' μ _ hμ`. Establish `h2 : (fun u v => Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(inner ℝ u (T v)) : ℂ))) = fun u v => Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(l (f.symm u) (f.symm v)) : ℂ))`. Use function extensionality and compare the values at `u v`. Rewrite using `[← hT]`.

Establish `h3 : μ.map f = m` using `huniq _ (by rw [h2]; exact h1)`. Rewrite using `[← h3, MeasureTheory.Measure.map_map hfm' hfm]`. Establish `: (f.symm ∘ f : V → V) = id`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.

Rewrite using `[this, MeasureTheory.Measure.map_id]`.
-/
theorem UpperTheory.Reformulated.B.Yzb9.existsUnique_of_equiv :
    ∀ {V W : Type} [inst : AddCommGroup V] [inst_1 : TopologicalSpace V] [IsTopologicalAddGroup V]
      [inst_3 : MeasurableSpace V] [BorelSpace V] [inst_5 : NormedAddCommGroup W] [inst_6 : NormedSpace ℝ W]
      [FiniteDimensional ℝ W] (e : V ≃+ W),
      Continuous (⇑e : V → W) →
        Continuous (⇑e.symm : W → V) →
          ∀ (l : V → V → ℝ),
            (∀ (x x' y : V), l (x + x') y = l x y + l x' y) →
              (∀ (x y : V), l x y = l y x) →
                (∀ (y : V), Continuous fun (x : V) ↦ l x y) →
                  (∀ (x : V), (∀ (y : V), l x y = (0 : ℝ)) → x = (0 : V)) →
                    ∃! μ : MeasureTheory.Measure V,
                      UpperTheory.Reformulated.B.Yzb9.SelfDual μ fun (x y : V) ↦
                        Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(l x y) : ℂ)) := by
  intro V W _ _ _ _ _ _ _ _ e he he' l hadd hsym hcont hnd
  let ψ := toEuclidean (E := W)
  let f : V ≃+ EuclideanSpace ℝ (Fin (Module.finrank ℝ W)) := e.trans ψ.toLinearEquiv.toAddEquiv
  have hf : Continuous f := ψ.continuous.comp he
  have hf' : Continuous f.symm := he'.comp ψ.symm.continuous
  obtain ⟨T, hT⟩ := UpperTheory.Reformulated.B.Yzb9.exists_strictHenselian_absolutely_closed_local_ring (fun u v => l (f.symm u) (f.symm v))
    (fun u u' v => by simp only [map_add, hadd]) (fun u v => hsym _ _)
    (fun v => (hcont _).comp hf')
    (fun u hu => by
      have : f.symm u = 0 := hnd _ (fun y => by
        have := hu (f y)
        simpa using this)
      simpa using this)
  have hTs : ∀ u v, inner ℝ u (T v) = inner ℝ (T u) v := by
    intro u v
    rw [← hT, hsym, hT, real_inner_comm]
  obtain ⟨m, hm, huniq⟩ := UpperTheory.Reformulated.B.Yzb9.existsUnique_E T hTs
  have hfm : Measurable f := hf.measurable
  have hfm' : Measurable f.symm := hf'.measurable
  refine ⟨m.map f.symm, ?_, ?_⟩
  · have h1 := UpperTheory.Reformulated.B.Yzb9.selfDual_map f.symm hf' hf m _ hm
    have h2 : (fun (x y : V) => Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(l x y) : ℂ))) =
        fun x y => Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I *
          (↑(inner ℝ (f.symm.symm x) (T (f.symm.symm y))) : ℂ)) := by
      funext x y
      rw [← hT]
      simp
    change UpperTheory.Reformulated.B.Yzb9.SelfDual (m.map f.symm) _
    rw [h2]
    exact h1
  · intro μ hμ
    have h1 := UpperTheory.Reformulated.B.Yzb9.selfDual_map f hf hf' μ _ hμ
    have h2 : (fun u v => Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(inner ℝ u (T v)) : ℂ))) =
        fun u v => Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I *
          (↑(l (f.symm u) (f.symm v)) : ℂ)) := by
      funext u v
      rw [← hT]
    have h3 : μ.map f = m := huniq _ (by rw [h2]; exact h1)
    rw [← h3, MeasureTheory.Measure.map_map hfm' hfm]
    have : (f.symm ∘ f : V → V) = id := by
      funext x
      simp
    rw [this, MeasureTheory.Measure.map_id]
