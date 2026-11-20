import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionOffZerosDense
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermPrimitiveForm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedOffDiscriminant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionSheetedClosureEquations
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem FiniteProjectionOffZerosDense.proof (hPF : IrreducibleGermPrimitiveForm.Statement)
    (hSh : PrimitiveFormSheetedOffDiscriminant.Statement)
    (hCl : FiniteProjectionSheetedClosureEquations.Statement) :
    FiniteProjectionOffZerosDense.Statement := by
  intro σ _ X w d A hX hirr hiso hinj δ hδ hδne
  obtain ⟨ℓ, N, a, δ₀, q, ha, hδ₀, hq, hδ₀ne, hp, hsep, hcoord⟩ := hPF σ X w d A hX hirr hiso hinj
  obtain ⟨M, hM, hMsh⟩ := hSh σ X w d A hX hirr hiso hinj ℓ N a δ₀ q ha hδ₀ hq hδ₀ne hp hsep hcoord
  obtain ⟨m, c, hc, hcY, hcl⟩ := hCl σ X w d A hX hiso hinj (fun y => δ₀ y * δ y) (hδ₀.mul hδ)
    ⟨M, hM, fun y hy hne => hMsh y hy (left_ne_zero_of_mul hne)⟩
  have hcomp : ∀ {f : (Fin d → ℂ) → ℂ}, AnalyticAt ℂ f (A w) → AnalyticAt ℂ (fun z => f (A z)) w :=
    fun hf => hf.comp (A.analyticAt w)
  have hnot : ∀ {f : (Fin d → ℂ) → ℂ}, AnalyticAt ℂ f (A w) → (¬ ∀ᶠ y in 𝓝 (A w), f y = 0) →
      ¬ ∀ᶠ z in 𝓝 w, z ∈ X → f (A z) = 0 := fun hf hne h => hne (hinj _ hf h)
  have hvan : ∀ k, ∀ᶠ z in 𝓝 w, z ∈ X → c k z = 0 := by
    intro k
    have h1 : ∀ᶠ z in 𝓝 w, z ∈ X → (c k z * δ₀ (A z)) * δ (A z) = 0 := by
      filter_upwards [hcY] with z hz hzX
      by_cases h : δ₀ (A z) * δ (A z) = 0
      · rw [mul_assoc, h, mul_zero]
      · rw [hz hzX h k, zero_mul, zero_mul]
    rcases hirr.2 (fun z => c k z * δ₀ (A z)) (fun z => δ (A z)) ((hc k).mul (hcomp hδ₀)) (hcomp hδ)
      h1 with h2 | h2
    · rcases hirr.2 (c k) (fun z => δ₀ (A z)) (hc k) (hcomp hδ₀) h2 with h3 | h3
      · exact h3
      · exact absurd h3 (hnot hδ₀ hδ₀ne)
    · exact absurd h2 (hnot hδ hδne)
  have hall : ∀ᶠ z in 𝓝 w, z ∈ X → ∀ k, c k z = 0 := by
    filter_upwards [Filter.eventually_all.2 hvan] with z hz hzX k using hz k hzX
  refine ⟨_, hall.and hcl, ?_⟩
  rintro z ⟨hzX, hz1, hz2⟩
  refine closure_mono ?_ (hz2 hzX (hz1 hzX))
  rintro x ⟨hx, hne⟩
  exact ⟨hx, right_ne_zero_of_mul hne⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
