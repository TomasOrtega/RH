import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticWeilFourierCompSmul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FQuadraticWeilFourierCompSmul.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.quadraticWeilFourier_comp_smul : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (s : A.Kˣ) (φ : A.L → ℂ), IsTest φ → ∀ y, fOp A ψ x μ (fun y' => φ ((s : A.K) • y')) y = ((A.absK s : ℂ) ^ 2)⁻¹ * fOp A ψ x μ φ (((s⁻¹ : A.Kˣ) : A.K) • y) := by
  first | exact @GlobalTheory.JR.WeilQuad.fOp_comp_smul | exact GlobalTheory.JR.WeilQuad.fOp_comp_smul | (intros; apply GlobalTheory.JR.WeilQuad.fOp_comp_smul <;> assumption)
