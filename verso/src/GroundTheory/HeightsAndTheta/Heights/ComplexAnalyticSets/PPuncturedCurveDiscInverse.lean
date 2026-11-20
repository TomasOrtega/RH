import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPuncturedCurveDiscInverse
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveCoordinateGraph
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicDerivNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

/- English proof (translation)
Introduce `n I q hrad hdim`. Take `⟨ε, hε, hgraph⟩` from `hG n I q hrad hdim`. Use `⟨ε, hε, fun φ σ₀ δ hδ hφd hφi hφZ hφε hφq ↦ ?_⟩` and prove the remaining obligations. Establish `hσ₀ : σ₀ ∈ Metric.ball σ₀ δ` using `Metric.mem_ball_self hδ`. Take `⟨-, W, hWo, hxW, i, V, g, -, -, -, hW⟩` from `hgraph (φ σ₀) (hφZ hσ₀) hφε hφq`.

Use `set f : ℂ → ℂ := fun σ ↦ φ σ i with hf`. Use `set D : Set ℂ := Metric.ball σ₀ δ ∩ φ ⁻¹' W with hDdef`. Establish `hDo : IsOpen D` using `hφd.continuousOn.isOpen_inter_preimage Metric.isOpen_ball hWo`. Establish `hσD : σ₀ ∈ D` using `⟨hσ₀, hxW⟩`. Establish `hφg : ∀ σ ∈ D, g (f σ) = φ σ` using `fun σ hσ ↦ ((hW _ hσ.2).1 (hφZ hσ.1)).2`.

Establish `hfd : DifferentiableOn ℂ f D` using `(differentiableOn_pi.1 hφd i).mono Set.inter_subset_left`. Establish `hfi : Set.InjOn f D` using `fun s hs t ht h ↦ hφi hs.1 ht.1 (by rw [← hφg s hs, ← hφg t ht, h])`. Establish `hfa : AnalyticAt ℂ f σ₀` using `hfd.analyticAt (hDo.mem_nhds hσD)`. Establish `hf' : deriv f σ₀ ≠ 0` using `hD D f hDo hfd hfi σ₀ hσD`. Use `set h := hfa.hasStrictDerivAt.localInverse f (deriv f σ₀) σ₀ hf' with hhdef`.

Establish `hha : AnalyticAt ℂ h (f σ₀)` using `hfa.analyticAt_localInverse hf'`. Establish `hh0 : h (f σ₀) = σ₀` using `HasStrictFDerivAt.localInverse_apply_image ..`. Establish `hev : ∀ᶠ y in 𝓝 (f σ₀), AnalyticAt ℂ h y ∧ f (h y) = y ∧ h y ∈ D` using `hha.eventually_analyticAt.and ((hfa.hasStrictDerivAt.eventually_right_inverse hf').and (hha.continuousAt.preimage_mem_nhds (by rw [hh0]; exact hDo.mem_nhds hσD)))`. Take `⟨T, hTsub, hTo, hT⟩` from `mem_nhds_iff.1 hev`. Use `⟨W ∩ (fun z ↦ z i) ⁻¹' T, hWo.inter (hTo.preimage (continuous_apply i)), ⟨hxW, hT⟩, fun z ↦ h (z i), fun z hz ↦ ?_, fun z ⟨hzZ, hzW, hzT⟩ ↦ ?_⟩` and prove the remaining obligations.

Conclude with `((hTsub hz.2).1.differentiableAt.comp z (differentiableAt_apply i z)).differentiableWithinAt`. Take `⟨-, hfh, hhD⟩` from `hTsub hzT`. Use `⟨h (z i), hhD.1, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[← hφg _ hhD, hfh]`. Conclude with `((hW z hzW).1 hzZ).2`.
-/
theorem PuncturedCurveDiscInverse.proof (hG : CurveCoordinateGraph.Statement)
    (hD : InjectiveHolomorphicDerivNeZero.Statement) : PuncturedCurveDiscInverse.Statement := by
  intro n I q hrad hdim
  obtain ⟨ε, hε, hgraph⟩ := hG n I q hrad hdim
  refine ⟨ε, hε, fun φ σ₀ δ hδ hφd hφi hφZ hφε hφq ↦ ?_⟩
  have hσ₀ : σ₀ ∈ Metric.ball σ₀ δ := Metric.mem_ball_self hδ
  obtain ⟨-, W, hWo, hxW, i, V, g, -, -, -, hW⟩ := hgraph (φ σ₀) (hφZ hσ₀) hφε hφq
  set f : ℂ → ℂ := fun σ ↦ φ σ i with hf
  set D : Set ℂ := Metric.ball σ₀ δ ∩ φ ⁻¹' W with hDdef
  have hDo : IsOpen D := hφd.continuousOn.isOpen_inter_preimage Metric.isOpen_ball hWo
  have hσD : σ₀ ∈ D := ⟨hσ₀, hxW⟩
  have hφg : ∀ σ ∈ D, g (f σ) = φ σ := fun σ hσ ↦ ((hW _ hσ.2).1 (hφZ hσ.1)).2
  have hfd : DifferentiableOn ℂ f D := (differentiableOn_pi.1 hφd i).mono Set.inter_subset_left
  have hfi : Set.InjOn f D := fun s hs t ht h ↦ hφi hs.1 ht.1 (by rw [← hφg s hs, ← hφg t ht, h])
  have hfa : AnalyticAt ℂ f σ₀ := hfd.analyticAt (hDo.mem_nhds hσD)
  have hf' : deriv f σ₀ ≠ 0 := hD D f hDo hfd hfi σ₀ hσD
  set h := hfa.hasStrictDerivAt.localInverse f (deriv f σ₀) σ₀ hf' with hhdef
  have hha : AnalyticAt ℂ h (f σ₀) := hfa.analyticAt_localInverse hf'
  have hh0 : h (f σ₀) = σ₀ := HasStrictFDerivAt.localInverse_apply_image ..
  have hev : ∀ᶠ y in 𝓝 (f σ₀), AnalyticAt ℂ h y ∧ f (h y) = y ∧ h y ∈ D :=
    hha.eventually_analyticAt.and ((hfa.hasStrictDerivAt.eventually_right_inverse hf').and
      (hha.continuousAt.preimage_mem_nhds (by rw [hh0]; exact hDo.mem_nhds hσD)))
  obtain ⟨T, hTsub, hTo, hT⟩ := mem_nhds_iff.1 hev
  refine ⟨W ∩ (fun z ↦ z i) ⁻¹' T, hWo.inter (hTo.preimage (continuous_apply i)), ⟨hxW, hT⟩,
    fun z ↦ h (z i), fun z hz ↦ ?_, fun z ⟨hzZ, hzW, hzT⟩ ↦ ?_⟩
  · exact ((hTsub hz.2).1.differentiableAt.comp z (differentiableAt_apply i z)).differentiableWithinAt
  · obtain ⟨-, hfh, hhD⟩ := hTsub hzT
    refine ⟨h (z i), hhD.1, ?_, rfl⟩
    rw [← hφg _ hhD, hfh]
    exact ((hW z hzW).1 hzZ).2

end GroundTheory.Heights₂.Heights
