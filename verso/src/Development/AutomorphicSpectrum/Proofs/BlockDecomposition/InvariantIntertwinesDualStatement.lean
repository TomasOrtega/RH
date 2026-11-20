import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantIntertwinesDual
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FInvariantIntertwinesDual.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.invariant_intertwines_dual : ∀ {n : ℕ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (Kf : Fin n → Fin n → Module.End ℂ V), IsDerivK σ Kf → ∀ (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)), IsDualFam E G → ∀ t ∈ invA σ E, ∀ a b ξ, t (G a b ξ) = Kf a b (t ξ) := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.Intertw.intertwines | exact GlobalTheory.CompanionTheory.RealCountG.Intertw.intertwines | (intros; apply GlobalTheory.CompanionTheory.RealCountG.Intertw.intertwines <;> assumption)
