import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordHighestWeightVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.DiracK.dirac_ineq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCliffordHighestWeightVector.lean&line=624#L624)
-/
theorem _root_.GlobalTheory.T.clifford_highest_weight_vector : ∀ {n : ℕ} (lam : Fin n → ℤ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V),
    IsCoreMod (infOf lam) E1 E2 σ A → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ),
      IsCliff c → ∀ (τ : Fin n → ℝ) (x : ι → V), x ≠ 0 → Formalism.REAL.KHighest (fun _ => true) (yF (kF E1 E2) c) τ x →
        ∑ a, (m0 lam a) ^ 2 ≤ ∑ a, (τ a + rhoV n a) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.DiracK.dirac_ineq | exact GlobalTheory.CompanionTheory.DiracK.dirac_ineq | (intros; apply GlobalTheory.CompanionTheory.DiracK.dirac_ineq <;> assumption)
