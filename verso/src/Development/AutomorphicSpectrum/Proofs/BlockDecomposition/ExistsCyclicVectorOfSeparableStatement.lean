import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCyclicVectorOfSeparable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsCyclicVectorOfSeparable.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.exists_cyclic_vector_of_separable : ∀ (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K), γ.charpoly.Separable → ∃ v : Fin n → K, ∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.CyclicVector.exists_cyclic_vector | exact GlobalTheory.CompanionTheory.TorusCh.CyclicVector.exists_cyclic_vector | (intros; apply GlobalTheory.CompanionTheory.TorusCh.CyclicVector.exists_cyclic_vector <;> assumption)
