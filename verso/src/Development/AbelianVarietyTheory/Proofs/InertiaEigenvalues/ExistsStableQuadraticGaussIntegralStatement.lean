import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableQuadraticGaussIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.WeilQuad.exists_stableGauss` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsStableQuadraticGaussIntegral.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.exists_stable_quadraticGaussIntegral : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ u : A.Kˣ, ∃ G, IsStableGauss A ψ x μ u G := by
  first | exact @GlobalTheory.JR.WeilQuad.exists_stableGauss | exact GlobalTheory.JR.WeilQuad.exists_stableGauss | (intros; apply GlobalTheory.JR.WeilQuad.exists_stableGauss <;> assumption)
