import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepEvalZeroMemInduced
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWeilRepEvalZeroMemInduced.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.weilRep_evalZero_mem_induced : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L) (γ : ℂ) W, A.IsWeil ψ x A.etaK μ γ W → ∀ φ, IsTest φ → A.InI (fun g => W g φ 0) ∧ (φ ≠ 0 → γ ≠ 0) := by
  first | exact @GlobalTheory.WeilSmooth.jx_mem_induced | exact GlobalTheory.WeilSmooth.jx_mem_induced | (intros; apply GlobalTheory.WeilSmooth.jx_mem_induced <;> assumption)
