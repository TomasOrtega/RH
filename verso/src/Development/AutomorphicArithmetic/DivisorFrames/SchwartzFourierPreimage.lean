import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
open MeasureTheory FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB
open scoped FourierTransform SchwartzMap

/- English proof (translation)
Introduce `J _ β hβ hc`. Set `e : PiLp 2 (fun _ : J => ℂ) ≃L[ℝ] (J → ℂ)` to `PiLp.continuousLinearEquiv 2 ℝ _`. Set `σ : (J → ℂ) ≃L[ℝ] (J → ℂ)` to `ContinuousLinearEquiv.piCongrRight fun _ => Complex.conjCLE`. Set `b : 𝓢(J → ℂ, ℂ)` to `hc.toSchwartzMap hβ`. Set `g : 𝓢(PiLp 2 (fun _ : J => ℂ), ℂ)` to `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (e.trans σ) b`.

Set `G : 𝓢(PiLp 2 (fun _ : J => ℂ), ℂ)` to `𝓕 g`. Set `μ : Measure (J → ℂ)` to `Measure.map e volume`. Use `haveI : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map _`. Set `c : NNReal` to `Measure.addHaarScalarFactor μ volume`. Establish `hμ : μ = c • volume` using `Measure.isAddLeftInvariant_eq_smul _ _`.

Set `H : 𝓢(J → ℂ, ℂ)` to `((c : ℝ) : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm G`. Use `⟨H, H.continuous, fun N => ?_, fun x => ?_⟩` and prove the remaining obligations. Simplify using `only [add_comm (1 : ℝ), add_pow, one_pow, mul_one, Finset.sum_mul]`. Use `integrable_finsetSum _ fun k _ => ?_` and prove the remaining obligations. Use `(H.integrable_pow_mul volume k).mul_const (N.choose k : ℝ)` as an intermediate fact.

Use `this.congr (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : FT H (-x) = ∫ s, G (e.symm s) * ec (s * -x) ∂μ`. Rewrite using `[hμ, integral_smul_nnreal_measure, FT, NNReal.smul_def, ← integral_smul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations.

Simplify using `[H, mul_assoc]`. Establish `h2 : ∫ s, G (e.symm s) * ec (s * -x) ∂μ = ∫ v, G v * ec (e v * -x)`. Use `integral_map_equiv (μ := volume) e.toHomeomorph.toMeasurableEquiv (fun s => G (e.symm s) * ec (s * -x))` as an intermediate fact. Simplify using `using this`. Establish `h3 : (𝓕⁻ G : 𝓢(PiLp 2 (fun _ : J => ℂ), ℂ)) = g` using `FourierTransform.fourierInv_fourier_eq g`.

Establish `h4 : g (e.symm (σ x)) = β x`. Establish `: σ (σ x) = x`. Use extensionality with `j`. Simplify using `[σ]`. Simplify using `[g, b, this]`.

Rewrite using `[h1, h2, ← h4, ← h3, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']`. Use `integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Rewrite using `[mul_comm, ec]`. Use `congr 2`.

Simplify using `[PiLp.inner_apply, e, σ, Complex.inner]`. Simplify using `only [mul_comm (((v.ofLp _).re : ℝ) : ℂ), mul_comm (((v.ofLp _).im : ℝ) : ℂ)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.schwartz_fourier_preimage :
    ∀ {J : Type} [Fintype J] (β : (J → ℂ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) β → HasCompactSupport β →
        ∃ h : (J → ℂ) → ℂ, Continuous h ∧ (∀ N : ℕ, Integrable fun v => (1 + ‖v‖) ^ N * ‖h v‖) ∧ ∀ x, FT h (-x) = β x := by
  intro J _ β hβ hc
  let e : PiLp 2 (fun _ : J => ℂ) ≃L[ℝ] (J → ℂ) := PiLp.continuousLinearEquiv 2 ℝ _
  let σ : (J → ℂ) ≃L[ℝ] (J → ℂ) := ContinuousLinearEquiv.piCongrRight fun _ => Complex.conjCLE
  let b : 𝓢(J → ℂ, ℂ) := hc.toSchwartzMap hβ
  let g : 𝓢(PiLp 2 (fun _ : J => ℂ), ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (e.trans σ) b
  let G : 𝓢(PiLp 2 (fun _ : J => ℂ), ℂ) := 𝓕 g
  let μ : Measure (J → ℂ) := Measure.map e volume
  haveI : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map _
  let c : NNReal := Measure.addHaarScalarFactor μ volume
  have hμ : μ = c • volume := Measure.isAddLeftInvariant_eq_smul _ _
  let H : 𝓢(J → ℂ, ℂ) := ((c : ℝ) : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm G
  refine ⟨H, H.continuous, fun N => ?_, fun x => ?_⟩
  · simp only [add_comm (1 : ℝ), add_pow, one_pow, mul_one, Finset.sum_mul]
    refine integrable_finsetSum _ fun k _ => ?_
    have := (H.integrable_pow_mul volume k).mul_const (N.choose k : ℝ)
    refine this.congr (Filter.Eventually.of_forall fun v => ?_)
    ring
  · have h1 : FT H (-x) = ∫ s, G (e.symm s) * ec (s * -x) ∂μ := by
      rw [hμ, integral_smul_nnreal_measure, FT, NNReal.smul_def, ← integral_smul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp [H, mul_assoc]
    have h2 : ∫ s, G (e.symm s) * ec (s * -x) ∂μ = ∫ v, G v * ec (e v * -x) := by
      have := integral_map_equiv (μ := volume) e.toHomeomorph.toMeasurableEquiv (fun s => G (e.symm s) * ec (s * -x))
      simpa using this
    have h3 : (𝓕⁻ G : 𝓢(PiLp 2 (fun _ : J => ℂ), ℂ)) = g := FourierTransform.fourierInv_fourier_eq g
    have h4 : g (e.symm (σ x)) = β x := by
      have : σ (σ x) = x := by
        ext j
        simp [σ]
      simp [g, b, this]
    rw [h1, h2, ← h4, ← h3, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm, ec]
    congr 2
    simp [PiLp.inner_apply, e, σ, Complex.inner]
    simp only [mul_comm (((v.ofLp _).re : ℝ) : ℂ), mul_comm (((v.ofLp _).im : ℝ) : ℂ)]
    ring
