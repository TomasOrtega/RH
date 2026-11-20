import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Introduce `K _ _ n r _ _ μ _ φ ψ D hφ hD hDc hψ g`. Take `⟨C, hC, hFC⟩` from `exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)`. Set `f : (UPos n r → AdeleRing (𝓞 K) K) × archGroup K n → ℂ` to `fun p => φ (unipGL p.1 * g * infEmb K n p.2) * D p.2`. Establish `hfc : Continuous f`. Use `Continuous.mul (hφ.comp ?_) (hD.comp continuous_snd)` and prove the remaining obligations.

Conclude with `((continuous_unipGL.comp continuous_fst).mul continuous_const).mul (continuous_infEmb.comp continuous_snd)`. Establish `hint : Integrable f (((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod μ)`. Establish `h1 : IntegrableOn f (C ×ˢ tsupport D) ((unipMeasure K n r).prod μ)` using `hfc.continuousOn.integrableOn_compact (hC.prod hDc)`. Establish `h2 : IntegrableOn f (unipFundamentalDomain K n r ×ˢ Set.univ) ((unipMeasure K n r).prod μ)`. Use `h1.of_forall_diff_eq_zero (measurableSet_unipFundamentalDomain.prod MeasurableSet.univ) ?_` and prove the remaining obligations.

Introduce and unpack `⟨X, y⟩ ⟨⟨hX, -⟩, hn⟩`. Establish `hy : y ∉ tsupport D` using `fun hy => hn ⟨hFC hX, hy⟩`. Use `show φ (unipGL X * g * infEmb K n y) * D y = 0`. Rewrite using `[image_eq_zero_of_notMem_tsupport hy, mul_zero]`. Establish `h3 : ((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod μ = ((unipMeasure K n r).prod μ).restrict (unipFundamentalDomain K n r ×ˢ Set.univ)`.

Rewrite using `[← Measure.prod_restrict, Measure.restrict_univ]`. Rewrite using `[h3]`. Conclude with `h2`. Establish `key` using `integral_integral_swap (f := fun X y => φ (unipGL X * g * infEmb K n y) * D y) hint`. Use `show ∫ X in unipFundamentalDomain K n r, ψ (unipGL X * g) ∂unipMeasure K n r = ∫ y, (∫ X in unipFundamentalDomain K n r, φ (unipGL X * (g * infEmb K n y)) ∂unipMeasure K n r) * D y ∂μ`.

Repeatedly rewrite using `[hψ]`. Use `key.trans ?_` and prove the remaining obligations. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Use `show ∫ X in unipFundamentalDomain K n r, φ (unipGL X * g * infEmb K n y) * D y ∂unipMeasure K n r = (∫ X in unipFundamentalDomain K n r, φ (unipGL X * (g * infEmb K n y)) ∂unipMeasure K n r) * D y`. Rewrite using `[← integral_mul_const]`.

Repeatedly rewrite using `[mul_assoc]`.
-/
theorem UpperTheory.constantTerm_convolution_arch :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (μ : Measure (archGroup K n)) [μ.IsHaarMeasure] (φ ψ : AdelicGLn.AdelicGL K n → ℂ) (D : archGroup K n → ℂ), Continuous φ → Continuous D → HasCompactSupport D → (∀ g, ψ g = ∫ y, φ (g * infEmb K n y) * D y ∂μ) → ∀ g, constantTerm r ψ g = ∫ y, constantTerm r φ (g * infEmb K n y) * D y ∂μ := by
  intro K _ _ n r _ _ μ _ φ ψ D hφ hD hDc hψ g
  obtain ⟨C, hC, hFC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  let f : (UPos n r → AdeleRing (𝓞 K) K) × archGroup K n → ℂ :=
    fun p => φ (unipGL p.1 * g * infEmb K n p.2) * D p.2
  have hfc : Continuous f := by
    refine Continuous.mul (hφ.comp ?_) (hD.comp continuous_snd)
    exact ((continuous_unipGL.comp continuous_fst).mul continuous_const).mul
      (continuous_infEmb.comp continuous_snd)
  have hint : Integrable f (((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod μ) := by
    have h1 : IntegrableOn f (C ×ˢ tsupport D) ((unipMeasure K n r).prod μ) :=
      hfc.continuousOn.integrableOn_compact (hC.prod hDc)
    have h2 : IntegrableOn f (unipFundamentalDomain K n r ×ˢ Set.univ) ((unipMeasure K n r).prod μ) := by
      refine h1.of_forall_diff_eq_zero (measurableSet_unipFundamentalDomain.prod MeasurableSet.univ) ?_
      rintro ⟨X, y⟩ ⟨⟨hX, -⟩, hn⟩
      have hy : y ∉ tsupport D := fun hy => hn ⟨hFC hX, hy⟩
      show φ (unipGL X * g * infEmb K n y) * D y = 0
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    have h3 : ((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod μ
        = ((unipMeasure K n r).prod μ).restrict (unipFundamentalDomain K n r ×ˢ Set.univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [h3]
    exact h2
  have key := integral_integral_swap (f := fun X y => φ (unipGL X * g * infEmb K n y) * D y) hint
  show ∫ X in unipFundamentalDomain K n r, ψ (unipGL X * g) ∂unipMeasure K n r
    = ∫ y, (∫ X in unipFundamentalDomain K n r, φ (unipGL X * (g * infEmb K n y)) ∂unipMeasure K n r) * D y ∂μ
  simp_rw [hψ]
  refine key.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ∫ X in unipFundamentalDomain K n r, φ (unipGL X * g * infEmb K n y) * D y ∂unipMeasure K n r
    = (∫ X in unipFundamentalDomain K n r, φ (unipGL X * (g * infEmb K n y)) ∂unipMeasure K n r) * D y
  rw [← integral_mul_const]
  simp_rw [mul_assoc]
