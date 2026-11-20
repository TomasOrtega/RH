import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity

open MeasureTheory
open scoped Pointwise

namespace GlobalTheory

/- English proof (translation)
Establish `hsD : IsAddFundamentalDomain L (s +ᵥ D) volume` using `hD.vadd_of_comm s`. Establish `himg : (fun t => s + t) '' D = s +ᵥ D`. Express the relevant statement in the definitionally equal form `(fun t => s +ᵥ t) '' D = s +ᵥ D`. Conclude with `Set.image_vadd`. Rewrite using `[← (measurePreserving_add_left volume s).setIntegral_image_emb (MeasurableEquiv.addLeft s).measurableEmbedding g D, himg]`.

Use `hsD.setIntegral_eq hD (fun p x => ?_)` and prove the remaining obligations. Rewrite using `[AddSubgroup.vadd_def, vadd_eq_add, add_comm]`. Conclude with `hp p p.2 x`.
-/
theorem setIntegral_translate_of_periodic {n : Type} [Fintype n] (L : AddSubgroup (n → ℝ))
    [Countable L] (D : Set (n → ℝ)) (g : (n → ℝ) → ℂ)
    (hD : IsAddFundamentalDomain L D volume) (hp : ∀ p ∈ L, ∀ s, g (s + p) = g s)
    (s : n → ℝ) : ∫ t in D, g (s + t) = ∫ t in D, g t := by
  have hsD : IsAddFundamentalDomain L (s +ᵥ D) volume := hD.vadd_of_comm s
  have himg : (fun t => s + t) '' D = s +ᵥ D := by
    change (fun t => s +ᵥ t) '' D = s +ᵥ D
    exact Set.image_vadd
  rw [← (measurePreserving_add_left volume s).setIntegral_image_emb
    (MeasurableEquiv.addLeft s).measurableEmbedding g D, himg]
  refine hsD.setIntegral_eq hD (fun p x => ?_)
  rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
  exact hp p p.2 x

/- English proof (translation)
Introduce `n _ L L' _ _ D D' g hD hD' hDfin hD'fin hg ⟨C, hC⟩ hp hp'`. Establish `: IsFiniteMeasure (volume.restrict D)` using `⟨by rw [Measure.restrict_apply_univ]; exact hDfin⟩`. Establish `: IsFiniteMeasure (volume.restrict D')` using `⟨by rw [Measure.restrict_apply_univ]; exact hD'fin⟩`. Establish `hint : Integrable (Function.uncurry fun s t => g (s + t)) ((volume.restrict D).prod (volume.restrict D'))`. Use `Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun z => hC _)` and prove the remaining obligations.

Conclude with `(hg.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable`. Establish `h1 : ∫ s in D, ∫ t in D', g (s + t) = ((volume D).toReal : ℂ) * ∫ t in D', g t`. Repeatedly rewrite using `[setIntegral_translate_of_periodic L' D' g hD' hp']`. Rewrite using `[setIntegral_const]`. Simplify using `[Complex.real_smul, Measure.real]`.

Establish `h2 : ∫ t in D', ∫ s in D, g (s + t) = ((volume D').toReal : ℂ) * ∫ s in D, g s`. Establish `: ∀ t, ∫ s in D, g (s + t) = ∫ s in D, g s` using `fun t => by`. Repeatedly rewrite using `[add_comm _ t]`. Conclude with `setIntegral_translate_of_periodic L D g hD hp t`. Repeatedly rewrite using `[this]`.

Rewrite using `[setIntegral_const]`. Simplify using `[Complex.real_smul, Measure.real]`. Rewrite using `[← h1, ← h2]`. Conclude with `integral_integral_swap hint`.
-/
theorem mean_fundamentalDomain_eq_of_periodic :
    ∀ (n : Type) [Fintype n] (L L' : AddSubgroup (n → ℝ)) [Countable L] [Countable L'] (D D' : Set (n → ℝ)) (g : (n → ℝ) → ℂ), MeasureTheory.IsAddFundamentalDomain L D MeasureTheory.volume → MeasureTheory.IsAddFundamentalDomain L' D' MeasureTheory.volume → MeasureTheory.volume D < ⊤ → MeasureTheory.volume D' < ⊤ → Continuous g → (∃ C : ℝ, ∀ s, ‖g s‖ ≤ C) → (∀ p ∈ L, ∀ s, g (s + p) = g s) → (∀ p ∈ L', ∀ s, g (s + p) = g s) → ((MeasureTheory.volume D).toReal : ℂ) * ∫ s in D', g s = ((MeasureTheory.volume D').toReal : ℂ) * ∫ s in D, g s := by
  intro n _ L L' _ _ D D' g hD hD' hDfin hD'fin hg ⟨C, hC⟩ hp hp'
  have : IsFiniteMeasure (volume.restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hDfin⟩
  have : IsFiniteMeasure (volume.restrict D') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hD'fin⟩
  have hint : Integrable (Function.uncurry fun s t => g (s + t))
      ((volume.restrict D).prod (volume.restrict D')) := by
    refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun z => hC _)
    exact (hg.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
  have h1 : ∫ s in D, ∫ t in D', g (s + t) = ((volume D).toReal : ℂ) * ∫ t in D', g t := by
    simp_rw [setIntegral_translate_of_periodic L' D' g hD' hp']
    rw [setIntegral_const]
    simp [Complex.real_smul, Measure.real]
  have h2 : ∫ t in D', ∫ s in D, g (s + t) = ((volume D').toReal : ℂ) * ∫ s in D, g s := by
    have : ∀ t, ∫ s in D, g (s + t) = ∫ s in D, g s := fun t => by
      simp_rw [add_comm _ t]
      exact setIntegral_translate_of_periodic L D g hD hp t
    simp_rw [this]
    rw [setIntegral_const]
    simp [Complex.real_smul, Measure.real]
  rw [← h1, ← h2]
  exact integral_integral_swap hint

end GlobalTheory
