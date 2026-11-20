import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledIntegersKAnnihilatorSmallNearZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FScaledIntegersKAnnihilatorSmallNearZero.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.scaledIntegersK_annihilator_small_near_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ U ∈ 𝓝 (0 : A.K), ∀ᶠ c in 𝓝[≠] (0 : F), ∀ b : A.K, (∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1) → b ∈ U := by
  first | exact @GlobalTheory.JR.annihilator_small | exact GlobalTheory.JR.annihilator_small | (intros; apply GlobalTheory.JR.annihilator_small <;> assumption)
