import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalModularFormCuspForm
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

/- English proof (translation)
Introduce `M Γ k hM hle`. Conclude with `GlobalTheory.HeckeFamilyMatrices.finiteDimensional_modularForm_cuspForm Γ k (finiteIndex_of_Gamma_le hM hle)`.
-/
theorem finiteDimensional_of_Gamma_le :
    ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ →
      FiniteDimensional ℂ (ModularForm Γ k) ∧ FiniteDimensional ℂ (CuspForm Γ k) := by
  intro M Γ k hM hle
  exact GlobalTheory.HeckeFamilyMatrices.finiteDimensional_modularForm_cuspForm Γ k (finiteIndex_of_Gamma_le hM hle)

end GlobalTheory.OddFrame
