import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordVectorSpinWeight
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RealCount.spinM_vacuum_lowest` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCliffordVectorSpinWeight.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.clifford_vector_spin_weight : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ), IsCliff c →
    ∀ q : ι → ℂ, (∀ a b, a < b → c b a *ᵥ q = 0) →
    (∀ a, spinM c a a *ᵥ q = ((-(rhoV n a) : ℝ) : ℂ) • q) ∧ ∀ a b, a < b → spinM c b a *ᵥ q = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.spinM_vacuum_lowest | exact GlobalTheory.CompanionTheory.RealCount.spinM_vacuum_lowest | (intros; apply GlobalTheory.CompanionTheory.RealCount.spinM_vacuum_lowest <;> assumption)
