import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

/- English proof (translation)
Establish `: Countable F` using `Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)`. Establish `: Countable (𝓞 F)` using `inferInstanceAs (Countable {x : F // x ∈ integralClosure ℤ F})`. Establish `hs : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F)))`. Introduce `I`. Take `⟨s, hs⟩` from `(IsNoetherian.noetherian I : I.FG)`.

Conclude with `⟨s, hs⟩`. Establish `: Countable (Ideal (𝓞 F))` using `hs.countable`. Conclude with `Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) (fun v w h => HeightOneSpectrum.ext h)`.
-/
theorem placesCountable (F : Type) [Field F] [NumberField F] : Countable (HeightOneSpectrum (𝓞 F)) := by
  have : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  have : Countable (𝓞 F) := inferInstanceAs (Countable {x : F // x ∈ integralClosure ℤ F})
  have hs : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    exact ⟨s, hs⟩
  have : Countable (Ideal (𝓞 F)) := hs.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v w h => HeightOneSpectrum.ext h)

/- English proof (translation)
Use `haveI : BorelSpace (Af F) := ⟨rfl⟩`. Use `haveI := placesCountable F`. Establish `hset : intF (F` using `F) S = ⋂ v : HeightOneSpectrum (𝓞 F), ⋂ _ : v ∉ S, {y : Af F | y v ∈ v.adicCompletionIntegers F} := by`. Use extensionality with `y`. Simplify using `[intF]`.

Rewrite using `[hset]`. Use `MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => ?_` and prove the remaining obligations. Establish `hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v))` using `Valued.isOpen_valuationSubring _`. Establish `hcont : Continuous fun y : Af F => y v` using `RestrictedProduct.continuous_eval v`. Conclude with `(hO.preimage hcont).measurableSet`.
-/
theorem measurableSet_intF (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSet (intF (F := F) S) := by
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI := placesCountable F
  have hset : intF (F := F) S = ⋂ v : HeightOneSpectrum (𝓞 F), ⋂ _ : v ∉ S,
      {y : Af F | y v ∈ v.adicCompletionIntegers F} := by
    ext y; simp [intF]
  rw [hset]
  refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => ?_
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hcont : Continuous fun y : Af F => y v := RestrictedProduct.continuous_eval v
  exact (hO.preimage hcont).measurableSet

/- English proof (translation)
Use `haveI : BorelSpace (AF F) := ⟨rfl⟩`. Use `haveI : BorelSpace (Af F) := ⟨rfl⟩`. Use `haveI := placesCountable F`. Take `⟨hψc, hψn, -, -⟩` from `hψ`. Establish `hchar : AEStronglyMeasurable (fun b : AF F => ψ (-(algebraMap F (AF F) t * b))) db` using `(hψc.comp (by fun_prop)).aestronglyMeasurable`.

Establish `hf : AEStronglyMeasurable (fun b : AF F => starT σ J ψ dx Φ b * ψ (-(algebraMap F (AF F) t * b))) db` using `hI.aestronglyMeasurable.mul hchar`. Establish `hsnd : Measurable (fun b : AF F => sndA F b)`. Establish `: Continuous (fun b : AF F => sndA F b)` using `continuous_snd`. Conclude with `this.measurable`. Unfold `coefS coefT`.

Use `tendsto_integral_filter_of_dominated_convergence (fun b => ‖starT σ J ψ dx Φ b‖) ?_ ?_ hI.norm ?_` and prove the remaining obligations. Use `Filter.Eventually.of_forall fun S => ?_` and prove the remaining obligations. Establish `hind : Measurable (fun b : AF F => (intF (F` using `F) S).indicator (fun _ => (1 : ℂ)) (sndA F b)) := (measurable_const.indicator (measurableSet_intF F S)).comp hsnd`. Conclude with `hind.aestronglyMeasurable.mul hf`. Use `Filter.Eventually.of_forall fun S => Filter.Eventually.of_forall fun b => ?_` and prove the remaining obligations.

Establish `h1 : ‖(intF (F` using `F) S).indicator (fun _ => (1 : ℂ)) (sndA F b)‖ ≤ 1 := by`. Apply the tactic sequence `by_cases h : sndA F b ∈ intF (F := F) S <;> simp [h]`. Rewrite using `[norm_mul, norm_mul, hψn, mul_one]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) h1)`. Use `Filter.Eventually.of_forall fun b => ?_` and prove the remaining obligations.

Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ (sndA F b) v ∈ v.adicCompletionIntegers F}.Finite` using `(sndA F b).2`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with S hS`. Establish `hmem : sndA F b ∈ intF (F` using `F) S := by`. Introduce `v hv`.

Assume the negation of the conclusion as `hcon`. Conclude with `hv (hS (hfin.mem_toFinset.2 hcon))`. Simplify using `[hmem]`.
-/
theorem coefS_tendsto (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (db : Measure (AF F))
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (hI : Integrable (starT σ J ψ dx Φ) db) (t : F) :
    Filter.Tendsto (fun S => Coef.coefS σ J ψ dx db Φ t S) Filter.atTop (nhds (coefT σ J ψ dx db Φ t)) := by
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI := placesCountable F
  obtain ⟨hψc, hψn, -, -⟩ := hψ
  have hchar : AEStronglyMeasurable (fun b : AF F => ψ (-(algebraMap F (AF F) t * b))) db :=
    (hψc.comp (by fun_prop)).aestronglyMeasurable
  have hf : AEStronglyMeasurable
      (fun b : AF F => starT σ J ψ dx Φ b * ψ (-(algebraMap F (AF F) t * b))) db :=
    hI.aestronglyMeasurable.mul hchar
  have hsnd : Measurable (fun b : AF F => sndA F b) := by
    have : Continuous (fun b : AF F => sndA F b) := continuous_snd
    exact this.measurable
  unfold coefS coefT
  refine tendsto_integral_filter_of_dominated_convergence (fun b => ‖starT σ J ψ dx Φ b‖) ?_ ?_ hI.norm ?_
  · refine Filter.Eventually.of_forall fun S => ?_
    have hind : Measurable (fun b : AF F => (intF (F := F) S).indicator (fun _ => (1 : ℂ)) (sndA F b)) :=
      (measurable_const.indicator (measurableSet_intF F S)).comp hsnd
    exact hind.aestronglyMeasurable.mul hf
  · refine Filter.Eventually.of_forall fun S => Filter.Eventually.of_forall fun b => ?_
    have h1 : ‖(intF (F := F) S).indicator (fun _ => (1 : ℂ)) (sndA F b)‖ ≤ 1 := by
      by_cases h : sndA F b ∈ intF (F := F) S <;> simp [h]
    rw [norm_mul, norm_mul, hψn, mul_one]
    exact (mul_le_of_le_one_left (norm_nonneg _) h1)
  · refine Filter.Eventually.of_forall fun b => ?_
    have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ (sndA F b) v ∈ v.adicCompletionIntegers F}.Finite :=
      (sndA F b).2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with S hS
    have hmem : sndA F b ∈ intF (F := F) S := by
      intro v hv
      by_contra hcon
      exact hv (hS (hfin.mem_toFinset.2 hcon))
    simp [hmem]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
