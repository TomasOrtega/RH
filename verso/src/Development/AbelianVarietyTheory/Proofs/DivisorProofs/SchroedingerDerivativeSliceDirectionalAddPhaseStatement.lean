import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerDerivativeSliceDirectionalAddPhase
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WeilL2Words.dS_adeleJoin_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchroedingerDerivativeSliceDirectionalAddPhase.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.schroedingerDerivative_slice_directional_add_phase : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      Differentiable ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.dS F ψ h Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          fderiv ℝ (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x h.1 +
            2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * Φ (GlobalTheory.WeilCont.adeleJoin F x y) := by
  first | exact @GlobalTheory.WeilL2Words.dS_adeleJoin_eq | exact GlobalTheory.WeilL2Words.dS_adeleJoin_eq | (intros; apply GlobalTheory.WeilL2Words.dS_adeleJoin_eq <;> assumption)
