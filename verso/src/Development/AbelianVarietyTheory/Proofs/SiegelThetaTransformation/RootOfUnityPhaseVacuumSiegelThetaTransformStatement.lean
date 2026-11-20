import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RootOfUnityPhaseVacuumSiegelThetaTransform
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FRootOfUnityPhaseVacuumSiegelThetaTransform.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.rootOfUnityPhaseVacuum_siegelThetaTransform : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ φ ψ → PV φ → PV ψ := by
  first | exact @GlobalTheory.Phase.WeilPV.pv_of_transS | exact GlobalTheory.Phase.WeilPV.pv_of_transS | (intros; apply GlobalTheory.Phase.WeilPV.pv_of_transS <;> assumption)
