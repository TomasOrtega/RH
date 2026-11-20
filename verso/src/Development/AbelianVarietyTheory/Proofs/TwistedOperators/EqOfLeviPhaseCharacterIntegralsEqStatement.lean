import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfLeviPhaseCharacterIntegralsEq
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PhaseApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FEqOfLeviPhaseCharacterIntegralsEq.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.eq_of_leviPhaseCharacter_integrals_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ N₁ N₂ : Mx D W.rank r → ℂ, Continuous N₁ → Continuous N₂ → Integrable N₁ μ → Integrable N₂ μ → (∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₁ u ∂μ = ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N₂ u ∂μ) → N₁ = N₂ := by
  first | exact @GlobalTheory.LeviNormInj.eq_of_phase_integral_eq | exact GlobalTheory.LeviNormInj.eq_of_phase_integral_eq | (intros; apply GlobalTheory.LeviNormInj.eq_of_phase_integral_eq <;> assumption)
