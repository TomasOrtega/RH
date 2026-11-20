import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeUnitaryAction
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FDerivativeUnitaryAction.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.derivative_unitary_action : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H), (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) → ∀ (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (Kf : Fin n → Fin n → Module.End ℂ V), IsDerivK σ Kf → (∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) → ∀ T : H →ₗ[ℂ] V, (∀ a b w, T (G a b w) = Kf a b (T w)) → ∀ k w, T (ρ k w) = σ k (T w) := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.IntegrateK.intertwines_unitary | exact GlobalTheory.CompanionTheory.RealCount.IntegrateK.intertwines_unitary | (intros; apply GlobalTheory.CompanionTheory.RealCount.IntegrateK.intertwines_unitary <;> assumption)
