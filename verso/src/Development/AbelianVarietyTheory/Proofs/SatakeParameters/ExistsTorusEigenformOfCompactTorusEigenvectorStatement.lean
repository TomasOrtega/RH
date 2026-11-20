import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorusEigenform.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsTorusEigenformOfCompactTorusEigenvector.lean&line=110#L110)
-/
theorem _root_.GlobalTheory.T.exists_torusEigenform_of_compactTorus_eigenvector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Fin n → kˣ) V) (x : V) (θ : Fin n → kˣ →* ℂˣ), IsSmooth ρ → HasFiniteLength ρ → (∀ i, IsSmoothChar (θ i)) → x ≠ 0 → (∀ t ∈ torusO k (Fin n), ρ t x = (torusChar θ t : ℂ) • x) → ∃ (ψ : Fin n → kˣ →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ t y, l (ρ t y) = (torusChar ψ t : ℂ) * l y) ∧ ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = θ i u := by
  first | exact @GlobalTheory.TorusEigenform.main | exact GlobalTheory.TorusEigenform.main | (intros; apply GlobalTheory.TorusEigenform.main <;> assumption)
