import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetInducedTwoCharacters
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FJacquetInducedTwoCharacters.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.jacquet_induced_two_characters : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), JacquetOfInducedFiltration k → IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → (∀ φ ψ : (jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  first | exact @GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional | exact GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional | (intros; apply GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional <;> assumption)
