import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodGA

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory Formalism.L2.Theta Formalism.L2.SG.RowDict

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Use `Formalism.IndefR.PeterssonHilbertSpace.countable_GQ (D.sp.Y 0)` as an intermediate fact. Use `Formalism.IndefR.PeterssonHilbertSpace.measurableMul_GA (D.sp.Y 0)` as an intermediate fact. Use `Formalism.IndefR.PeterssonHilbertSpace.borel_GA (D.sp.Y 0)` as an intermediate fact. Establish `hR : μ.IsMulRightInvariant` using `Formalism.IndefR.Eqv.unimodGA_holds (D.sp.Y 0) μ hH`. Set `e : X.B.I.GA ≃ᵐ GA D (D.sp.Y 0)` to `{ toEquiv := ι.symm.toEquiv, measurable_toFun := hιs, measurable_invFun := hι }`.

Establish `he : (e : X.B.I.GA → GA D (D.sp.Y 0)) = ι.symm` using `rfl`. Use `set 𝓕' : Set (GA D (D.sp.Y 0)) := ι.symm '' X.B.fund with h𝓕'def`. Establish `hpre : e ⁻¹' 𝓕' = X.B.fund`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, h𝓕'def, Set.mem_image]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hxy⟩`. Establish `: y = x` using `ι.symm.injective (by rw [hxy]; rfl)`. Conclude with `this ▸ hy`. Introduce `hx`.

Conclude with `⟨x, hx, rfl⟩`. Establish `h1 : ∫⁻ x, f (ι.symm x * t) ∂(muX X) = ENNReal.ofReal c * ∫⁻ y in 𝓕', f (y * t) ∂μ`. Establish `hm : Measure.map e (muX X) = (ENNReal.ofReal c • μ).restrict 𝓕'`. Rewrite using `[← hmap, ← he, MeasurableEquiv.restrict_map, hpre]`. Rewrite using `[show (∫⁻ x, f (ι.symm x * t) ∂(muX X)) = ∫⁻ y, f (y * t) ∂(Measure.map e (muX X)) from (lintegral_map_equiv (fun y => f (y * t)) e).symm, hm, Measure.restrict_smul, lintegral_smul_measure]`.

Both sides reduce to the same expression. Establish `hmp : MeasurePreserving (fun y : GA D (D.sp.Y 0) => y * t) μ μ` using `measurePreserving_mul_right μ t`. Establish `hemb : MeasurableEmbedding (fun y : GA D (D.sp.Y 0) => y * t)` using `(MeasurableEquiv.mulRight t).measurableEmbedding`. Establish `h2 : ∫⁻ y in 𝓕', f (y * t) ∂μ = ∫⁻ y in (fun y => y * t) '' 𝓕', f y ∂μ` using `hmp.setLIntegral_comp_emb hemb f 𝓕'`. Establish `himg : (fun y : GA D (D.sp.Y 0) => y * t) '' 𝓕' = (fun y => y * t⁻¹) ⁻¹' 𝓕'`.

Use extensionality with `z`. Simplify using `only [Set.mem_image, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `using hy`.

Introduce `hz`. Conclude with `⟨z * t⁻¹, hz, by simp⟩`. Establish `hFD : IsFundamentalDomain (GQ (D.sp.Y 0)) ((fun y => y * t) '' 𝓕') μ`. Rewrite using `[himg]`. Use `h𝓕'.preimage_of_equiv (measurePreserving_mul_right μ t⁻¹).quasiMeasurePreserving (e := id) Function.bijective_id ?_` and prove the remaining obligations.

Introduce `γ y`. Use `show (γ : GA D (D.sp.Y 0)) * y * t⁻¹ = (γ : GA D (D.sp.Y 0)) * (y * t⁻¹)`. Rewrite using `[mul_assoc]`. Establish `h3 : ∫⁻ y in (fun y => y * t) '' 𝓕', f y ∂μ = ∫⁻ y in 𝓕, f y ∂μ` using `hFD.setLIntegral_eq h𝓕 f (fun γ x => hf γ γ.2 x)`. Rewrite using `[h1, h2, h3]`.
-/
theorem lintegral_comp_symm_mul_eq_ofReal_mul_setLIntegral (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ)
    (hι : Measurable ι) (hιs : Measurable ι.symm)
    (hmap : Measure.map ι.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • μ)
    (hH : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ (D.sp.Y 0)) 𝓕 μ)
    (h𝓕' : IsFundamentalDomain (GQ (D.sp.Y 0)) (ι.symm '' X.B.fund) μ)
    (f : GA D (D.sp.Y 0) → ENNReal) (hf : ∀ γ ∈ GQ (D.sp.Y 0), ∀ x, f (γ * x) = f x) :
    ∫⁻ x, f (ι.symm x * t) ∂(muX X) = ENNReal.ofReal c * ∫⁻ y in 𝓕, f y ∂μ := by
  have := Formalism.IndefR.PeterssonHilbertSpace.countable_GQ (D.sp.Y 0)
  have := Formalism.IndefR.PeterssonHilbertSpace.measurableMul_GA (D.sp.Y 0)
  have := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (D.sp.Y 0)
  have hR : μ.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds (D.sp.Y 0) μ hH
  let e : X.B.I.GA ≃ᵐ GA D (D.sp.Y 0) :=
    { toEquiv := ι.symm.toEquiv, measurable_toFun := hιs, measurable_invFun := hι }
  have he : (e : X.B.I.GA → GA D (D.sp.Y 0)) = ι.symm := rfl
  set 𝓕' : Set (GA D (D.sp.Y 0)) := ι.symm '' X.B.fund with h𝓕'def
  have hpre : e ⁻¹' 𝓕' = X.B.fund := by
    ext x
    simp only [Set.mem_preimage, h𝓕'def, Set.mem_image]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := ι.symm.injective (by rw [hxy]; rfl)
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩

  have h1 : ∫⁻ x, f (ι.symm x * t) ∂(muX X) = ENNReal.ofReal c * ∫⁻ y in 𝓕', f (y * t) ∂μ := by
    have hm : Measure.map e (muX X) = (ENNReal.ofReal c • μ).restrict 𝓕' := by
      rw [← hmap, ← he, MeasurableEquiv.restrict_map, hpre]
    rw [show (∫⁻ x, f (ι.symm x * t) ∂(muX X)) = ∫⁻ y, f (y * t) ∂(Measure.map e (muX X)) from
      (lintegral_map_equiv (fun y => f (y * t)) e).symm, hm, Measure.restrict_smul, lintegral_smul_measure]
    rfl

  have hmp : MeasurePreserving (fun y : GA D (D.sp.Y 0) => y * t) μ μ := measurePreserving_mul_right μ t
  have hemb : MeasurableEmbedding (fun y : GA D (D.sp.Y 0) => y * t) :=
    (MeasurableEquiv.mulRight t).measurableEmbedding
  have h2 : ∫⁻ y in 𝓕', f (y * t) ∂μ = ∫⁻ y in (fun y => y * t) '' 𝓕', f y ∂μ :=
    hmp.setLIntegral_comp_emb hemb f 𝓕'
  have himg : (fun y : GA D (D.sp.Y 0) => y * t) '' 𝓕' = (fun y => y * t⁻¹) ⁻¹' 𝓕' := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hz
      exact ⟨z * t⁻¹, hz, by simp⟩
  have hFD : IsFundamentalDomain (GQ (D.sp.Y 0)) ((fun y => y * t) '' 𝓕') μ := by
    rw [himg]
    refine h𝓕'.preimage_of_equiv (measurePreserving_mul_right μ t⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id ?_
    intro γ y
    show (γ : GA D (D.sp.Y 0)) * y * t⁻¹ = (γ : GA D (D.sp.Y 0)) * (y * t⁻¹)
    rw [mul_assoc]
  have h3 : ∫⁻ y in (fun y => y * t) '' 𝓕', f y ∂μ = ∫⁻ y in 𝓕, f y ∂μ :=
    hFD.setLIntegral_eq h𝓕 f (fun γ x => hf γ γ.2 x)
  rw [h1, h2, h3]

/- English proof (translation)
Introduce `F hFc hinv hF`. Use `Formalism.IndefR.PeterssonHilbertSpace.borel_GA (D.sp.Y 0)` as an intermediate fact. Use `Formalism.IndefR.PeterssonHilbertSpace.measurableMul_GA (D.sp.Y 0)` as an intermediate fact. Establish `hmeasG : Measurable (fun x => F (ι.symm x * t))` using `hFc.measurable.comp ((measurable_mul_const t).comp hιs)`. Establish `hL` using `lintegral_comp_symm_mul_eq_ofReal_mul_setLIntegral μ 𝓕 X ι t c hι hιs hmap hH h𝓕 h𝓕' (fun y => ENNReal.ofReal (‖F y‖ ^ 2)) (fun γ hγ x => by simp only [hinv γ hγ x])`.

Establish `hint : Integrable (fun y => ‖F y‖ ^ 2) (μ.restrict 𝓕)` using `(memLp_two_iff_integrable_sq_norm hF.1).1 hF`. Establish `hfin : ∫⁻ y in 𝓕, ENNReal.ofReal (‖F y‖ ^ 2) ∂μ < ⊤` using `hint.lintegral_lt_top`. Establish `hasm : AEStronglyMeasurable (fun x => F (ι.symm x * t)) (muX X)` using `hmeasG.aestronglyMeasurable`. Establish `hint2 : Integrable (fun x => ‖F (ι.symm x * t)‖ ^ 2) (muX X)`. Use `⟨(continuous_pow 2).comp_aestronglyMeasurable hasm.norm, ?_⟩` and prove the remaining obligations.

Rewrite using `[hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => by positivity), hL]`. Conclude with `ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin`. Use `⟨(memLp_two_iff_integrable_sq_norm hasm).2 hint2, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => by positivity) hint2.aestronglyMeasurable, hL, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, ← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => by positivity) hint.aestronglyMeasurable]`.
-/
theorem squareIntegrableTransfer_of_fundamentalDomains (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ)
    (hι : Measurable ι) (hιs : Measurable ι.symm) (hc : 0 ≤ c)
    (hmap : Measure.map ι.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • μ)
    (hH : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ (D.sp.Y 0)) 𝓕 μ)
    (h𝓕' : IsFundamentalDomain (GQ (D.sp.Y 0)) (ι.symm '' X.B.fund) μ) :
    SquareIntegrableTransfer μ 𝓕 X ι t c := by
  intro F hFc hinv hF
  have := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (D.sp.Y 0)
  have := Formalism.IndefR.PeterssonHilbertSpace.measurableMul_GA (D.sp.Y 0)
  have hmeasG : Measurable (fun x => F (ι.symm x * t)) :=
    hFc.measurable.comp ((measurable_mul_const t).comp hιs)
  have hL := lintegral_comp_symm_mul_eq_ofReal_mul_setLIntegral μ 𝓕 X ι t c hι hιs hmap hH h𝓕 h𝓕' (fun y => ENNReal.ofReal (‖F y‖ ^ 2))
    (fun γ hγ x => by simp only [hinv γ hγ x])
  have hint : Integrable (fun y => ‖F y‖ ^ 2) (μ.restrict 𝓕) :=
    (memLp_two_iff_integrable_sq_norm hF.1).1 hF
  have hfin : ∫⁻ y in 𝓕, ENNReal.ofReal (‖F y‖ ^ 2) ∂μ < ⊤ := hint.lintegral_lt_top
  have hasm : AEStronglyMeasurable (fun x => F (ι.symm x * t)) (muX X) := hmeasG.aestronglyMeasurable
  have hint2 : Integrable (fun x => ‖F (ι.symm x * t)‖ ^ 2) (muX X) := by
    refine ⟨(continuous_pow 2).comp_aestronglyMeasurable hasm.norm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => by positivity), hL]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  refine ⟨(memLp_two_iff_integrable_sq_norm hasm).2 hint2, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => by positivity) hint2.aestronglyMeasurable, hL,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hc,
    ← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => by positivity) hint.aestronglyMeasurable]

/- English proof (translation)
Use `Formalism.IndefR.PeterssonHilbertSpace.measurableMul_GA (D.sp.Y 0)` as an intermediate fact. Take `⟨hmf, hcov, hdis⟩` from `X.B.fund_spec`. Set `e : X.B.I.GA ≃ᵐ GA D (D.sp.Y 0)` to `{ toEquiv := ι.symm.toEquiv, measurable_toFun := hιs, measurable_invFun := hι }`. Establish `hset : ι.symm '' X.B.fund = ι ⁻¹' X.B.fund`. Use extensionality with `y`.

Simplify using `only [Set.mem_image, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Simplify using `using hx`. Introduce `hy`.

Conclude with `⟨ι y, hy, by simp⟩`. Establish `hnull : ∀ A : Set X.B.I.GA, X.B.I.muA X.B.μf A = 0 → μ (ι ⁻¹' A) = 0`. Introduce `A hA`. Establish `h1 : Measure.map e (X.B.I.muA X.B.μf) (ι ⁻¹' A) = X.B.I.muA X.B.μf A`. Rewrite using `[MeasurableEquiv.map_apply]`.

Use `congr 1`. Use extensionality with `x`. Simplify using `[e]`. Establish `h2 : (ENNReal.ofReal c • μ) (ι ⁻¹' A) = 0`. Rewrite using `[← hmap]`.

Conclude with `h1.trans hA`. Rewrite `h2` using `[Measure.smul_apply, smul_eq_mul, mul_eq_zero]`. Break down `h2 with h | h` into its components or cases. Conclude with `absurd h (by simpa using hc)`. Conclude with `h`.

Rewrite using `[hset]`. Use `IsFundamentalDomain.mk'' (hι hmf).nullMeasurableSet (ae_of_all _ ?_) ?_ ?_` and prove the remaining obligations. Introduce `y`. Take `⟨γ', hγ', hmem⟩` from `hcov (ι y)`. Use `⟨⟨ι.symm γ', (hrat _).2 (by simpa using hγ')⟩, ?_⟩` and prove the remaining obligations.

Use `show ι (ι.symm γ' * y) ∈ X.B.fund`. Simplify using `using hmem`. Introduce `γ hγ`. Establish `hγ1 : ι γ ≠ 1`. Introduce `h`.

Apply `hγ` to reduce the goal to its premises. Use `ext`. Simplify using `using congrArg ι.symm h`. Establish `h0` using `hdis (ι γ) ((hrat γ).1 γ.2) hγ1`. Use `(measure_mono_null ?_ (hnull _ h0) : μ _ = 0)` and prove the remaining obligations.

Introduce `y hy`. Take `⟨⟨z, hz, rfl⟩, hy2⟩` from `hy`. Use `⟨⟨ι z, hz, ?_⟩, hy2⟩` and prove the remaining obligations. Use `show ι γ * ι z = ι ((γ : GA D (D.sp.Y 0)) * z)`. Rewrite using `[map_mul]`.

Introduce `γ`. Conclude with `(measurePreserving_mul_left μ (γ : GA D (D.sp.Y 0))).quasiMeasurePreserving`.
-/
theorem fund_image_of (μ : Measure (GA D (D.sp.Y 0)))
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (c : ℝ)
    (hι : Measurable ι) (hιs : Measurable ι.symm) (hc : 0 < c)
    (hmap : Measure.map ι.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • μ)
    (hH : μ.IsHaarMeasure)
    (hrat : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ ι g ∈ X.B.I.GFset) :
    IsFundamentalDomain (GQ (D.sp.Y 0)) (ι.symm '' X.B.fund) μ := by
  have := Formalism.IndefR.PeterssonHilbertSpace.measurableMul_GA (D.sp.Y 0)
  obtain ⟨hmf, hcov, hdis⟩ := X.B.fund_spec
  let e : X.B.I.GA ≃ᵐ GA D (D.sp.Y 0) :=
    { toEquiv := ι.symm.toEquiv, measurable_toFun := hιs, measurable_invFun := hι }
  have hset : ι.symm '' X.B.fund = ι ⁻¹' X.B.fund := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨ι y, hy, by simp⟩

  have hnull : ∀ A : Set X.B.I.GA, X.B.I.muA X.B.μf A = 0 → μ (ι ⁻¹' A) = 0 := by
    intro A hA
    have h1 : Measure.map e (X.B.I.muA X.B.μf) (ι ⁻¹' A) = X.B.I.muA X.B.μf A := by
      rw [MeasurableEquiv.map_apply]
      congr 1
      ext x
      simp [e]
    have h2 : (ENNReal.ofReal c • μ) (ι ⁻¹' A) = 0 := by
      rw [← hmap]
      exact h1.trans hA
    rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h2
    rcases h2 with h | h
    · exact absurd h (by simpa using hc)
    · exact h
  rw [hset]
  refine IsFundamentalDomain.mk'' (hι hmf).nullMeasurableSet (ae_of_all _ ?_) ?_ ?_
  · intro y
    obtain ⟨γ', hγ', hmem⟩ := hcov (ι y)
    refine ⟨⟨ι.symm γ', (hrat _).2 (by simpa using hγ')⟩, ?_⟩
    show ι (ι.symm γ' * y) ∈ X.B.fund
    simpa using hmem
  · intro γ hγ
    have hγ1 : ι γ ≠ 1 := by
      intro h
      apply hγ
      ext
      simpa using congrArg ι.symm h
    have h0 := hdis (ι γ) ((hrat γ).1 γ.2) hγ1
    refine (measure_mono_null ?_ (hnull _ h0) : μ _ = 0)
    intro y hy
    obtain ⟨⟨z, hz, rfl⟩, hy2⟩ := hy
    refine ⟨⟨ι z, hz, ?_⟩, hy2⟩
    show ι γ * ι z = ι ((γ : GA D (D.sp.Y 0)) * z)
    rw [map_mul]
  · intro γ
    exact (measurePreserving_mul_left μ (γ : GA D (D.sp.Y 0))).quasiMeasurePreserving

/- English proof (translation)
The claim follows from `squareIntegrableTransfer_of_fundamentalDomains μ 𝓕 X ι t c hι hιs hc.le hmap hH h𝓕 (fund_image_of μ X ι c hι hιs hc hmap hH hrat)`.
-/
theorem squareIntegrableTransfer_of_rational_points (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ)
    (hι : Measurable ι) (hιs : Measurable ι.symm) (hc : 0 < c)
    (hmap : Measure.map ι.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • μ)
    (hH : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ (D.sp.Y 0)) 𝓕 μ)
    (hrat : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ ι g ∈ X.B.I.GFset) :
    SquareIntegrableTransfer μ 𝓕 X ι t c :=
  squareIntegrableTransfer_of_fundamentalDomains μ 𝓕 X ι t c hι hιs hc.le hmap hH h𝓕 (fund_image_of μ X ι c hι hιs hc hmap hH hrat)

/- English proof (translation)
Use `Formalism.IndefR.PeterssonHilbertSpace.borel_GA (D.sp.Y 0)` as an intermediate fact. Conclude with `⟨ι.continuous.measurable, ι.symm.continuous.measurable⟩`.
-/
theorem measurable_of_borel (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (ι : GA D (D.sp.Y 0) ≃ₜ* X.B.I.GA)
    (hB : BorelSpace X.B.I.GA) :
    Measurable (ι.toMulEquiv : GA D (D.sp.Y 0) → X.B.I.GA) ∧
      Measurable (ι.toMulEquiv.symm : X.B.I.GA → GA D (D.sp.Y 0)) := by
  have := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (D.sp.Y 0)
  exact ⟨ι.continuous.measurable, ι.symm.continuous.measurable⟩

end Formalism.IndefR.AutomorphicEvaluation

end
