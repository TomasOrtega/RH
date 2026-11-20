import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportPartialFourierGLBlock
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.fourG_hasCompactSupport` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FHasCompactSupportPartialFourierGLBlock.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.hasCompactSupport_partialFourierGLBlock : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f' : Gl r F → ℂ, IsTest f' → (∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) → HasCompactSupport (fourG M ψ f') := by
  first | exact @GlobalTheory.JR.fourG_hasCompactSupport | exact GlobalTheory.JR.fourG_hasCompactSupport | (intros; apply GlobalTheory.JR.fourG_hasCompactSupport <;> assumption)
