import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PFdRight

end MainStatements.WeightKernel.PFdRight

/- English proof (translation)
Introduce `G _ _ _ _ _ _ Γ _ μ _ _ 𝓕 h𝓕 F hF g`. Establish `h2 : IsFundamentalDomain Γ ((fun x : G => x * g⁻¹) ⁻¹' 𝓕) μ` using `h𝓕.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])`. Establish `key : ∫ x in 𝓕, F (x * g) ∂μ = ∫ x in (fun x : G => x * g⁻¹) ⁻¹' 𝓕, F x ∂μ`. Rewrite using `[← Set.image_mul_right, (measurePreserving_mul_right μ g).setIntegral_image_emb (measurableEmbedding_mulRight g) F 𝓕]`. Rewrite using `[key]`.

Conclude with `h2.setIntegral_eq h𝓕 (fun γ x => by rw [Subgroup.smul_def, smul_eq_mul]; exact hF γ γ.2 x)`.
-/
theorem MainStatements.WeightKernel.fdRight : MainStatements.WeightKernel.FDRight := by
  intro G _ _ _ _ _ _ Γ _ μ _ _ 𝓕 h𝓕 F hF g
  have h2 : IsFundamentalDomain Γ ((fun x : G => x * g⁻¹) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  have key : ∫ x in 𝓕, F (x * g) ∂μ = ∫ x in (fun x : G => x * g⁻¹) ⁻¹' 𝓕, F x ∂μ := by
    rw [← Set.image_mul_right,
      (measurePreserving_mul_right μ g).setIntegral_image_emb (measurableEmbedding_mulRight g) F 𝓕]
  rw [key]
  exact h2.setIntegral_eq h𝓕 (fun γ x => by rw [Subgroup.smul_def, smul_eq_mul]; exact hF γ γ.2 x)
