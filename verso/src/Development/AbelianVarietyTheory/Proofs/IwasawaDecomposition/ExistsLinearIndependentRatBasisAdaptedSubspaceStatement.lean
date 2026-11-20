import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinearIndependentRatBasisAdaptedSubspace
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsLinearIndependentRatBasisAdaptedSubspace.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_linearIndependent_rat_basis_adapted_subspace : ∀ (g r : ℕ) (I L : Submodule ℚ (Fin r → ℚ)), I ≤ L → Module.finrank ℚ L = g → ∃ rk : ℕ, rk ≤ g ∧ ∃ ε : Fin g → Fin r → ℚ, LinearIndependent ℚ ε ∧ (∀ i, ε i ∈ L) ∧ (∀ i : Fin g, i.val < rk → ε i ∈ I) ∧ ∀ x ∈ I, x ∈ Submodule.span ℚ (ε '' {i | i.val < rk}) := by
  first | exact @GlobalTheory.adapted_basis_extension | exact GlobalTheory.adapted_basis_extension | (intros; apply GlobalTheory.adapted_basis_extension <;> assumption)
