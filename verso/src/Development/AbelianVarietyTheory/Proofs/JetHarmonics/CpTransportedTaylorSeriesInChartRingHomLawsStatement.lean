import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MomOne.TaylorRead.hat_laws` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FCpTransportedTaylorSeriesInChartRingHomLaws.lean&line=115#L115)
-/
theorem _root_.GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧), constantCoeff ℓ = 0 → (∀ F G : ℂ → ℂ, AnalyticAt ℂ F 0 → AnalyticAt ℂ G 0 → hat ι ℓ (fun z => F z + G z) = hat ι ℓ F + hat ι ℓ G ∧ hat ι ℓ (fun z => F z * G z) = hat ι ℓ F * hat ι ℓ G ∧ ((∀ᶠ z in 𝓝[≠] (0 : ℂ), F z = G z) → hat ι ℓ F = hat ι ℓ G) ∧ (coeff 1 ℓ ≠ 0 → hat ι ℓ F = hat ι ℓ G → F =ᶠ[𝓝 0] G)) ∧ (∀ c : ℂ, hat ι ℓ (fun _ => c) = C (ι c)) ∧ hat ι ℓ (fun z => z) = ℓ ∧ (∀ F : ℂ → ℂ, constantCoeff (hat ι ℓ F) = ι (F 0)) ∧ (∀ F : ℂ → ℂ, AnalyticAt ℂ F 0 → derivative ℂ_[q] (hat ι ℓ F) = derivative ℂ_[q] ℓ * hat ι ℓ (deriv F)) ∧ (∀ (F : ℂ → ℂ) (α : ℂ), AnalyticAt ℂ F 0 → hat ι ℓ (fun z => F (α * z)) = hat ι (C (ι α) * ℓ) F) ∧ ∀ (F : ℂ → ℂ) (h : ℂ_[q]⟦X⟧), constantCoeff h = 0 → (hat ι ℓ F).subst h = hat ι (ℓ.subst h) F := by
  first | exact @GlobalTheory.MomOne.TaylorRead.hat_laws | exact GlobalTheory.MomOne.TaylorRead.hat_laws | (intros; apply GlobalTheory.MomOne.TaylorRead.hat_laws <;> assumption)
