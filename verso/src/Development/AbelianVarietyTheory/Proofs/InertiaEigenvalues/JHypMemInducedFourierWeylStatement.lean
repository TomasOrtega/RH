import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JHypMemInducedFourierWeyl
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FJHypMemInducedFourierWeyl.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.jHyp_mem_induced_fourier_weyl : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ', IsTest φ' → A.InI (A.jHyp μK ψ φ') ∧ ∀ h, A.jHyp μK ψ (A.fourK μK ψ φ') h = A.jHyp μK ψ φ' (h * wS A.K) := by
  first | exact @GlobalTheory.JR.HypJ.main | exact GlobalTheory.JR.HypJ.main | (intros; apply GlobalTheory.JR.HypJ.main <;> assumption)
