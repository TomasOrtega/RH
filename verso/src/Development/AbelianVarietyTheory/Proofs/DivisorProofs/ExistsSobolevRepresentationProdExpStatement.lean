import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSobolevRepresentationProdExp
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_sobolev_representation_prodExp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSobolevRepresentationProdExp.lean&line=131#L131)
-/
theorem _root_.GlobalTheory.T.exists_sobolev_representation_prodExp' : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (ε : ℝ), 0 < ε → ∀ (n : ℕ) (X : Fin n → 𝔤), ∃ (N : ℕ) (l : Fin N → List 𝔤) (κ : Fin N → (Fin n → ℝ) → ℂ), (∀ i, Continuous (κ i) ∧ tsupport (κ i) ⊆ Metric.closedBall 0 ε) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ g, f g = ∑ i, ∫ t, κ i t * (l i).foldr h.rightDeriv f (g * h.prodExp X t) := by
  first | exact @GlobalTheory.exists_sobolev_representation_prodExp | exact GlobalTheory.exists_sobolev_representation_prodExp | (intros; apply GlobalTheory.exists_sobolev_representation_prodExp <;> assumption)
