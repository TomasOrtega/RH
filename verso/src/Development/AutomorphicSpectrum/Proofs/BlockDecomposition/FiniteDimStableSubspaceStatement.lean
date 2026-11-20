import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimStableSubspace
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.IrredMod.exists_finiteDimensional_zalg_lie_stable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteDimStableSubspace.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.finite_dim_stable_subspace : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (W : Submodule ℂ (Sm E a)), IsStable W → (∀ φ ∈ W, IsAutForm φ) → ∀ φ ∈ W, ∃ Y : Submodule ℂ (Sm E a), FiniteDimensional ℂ Y ∧ Y ≤ W ∧ φ ∈ Y ∧ (∀ z ∈ Zalg E a, ∀ y ∈ Y, z y ∈ Y) ∧ ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ y ∈ Y, lie E a X y ∈ Y := by
  first | exact @GlobalTheory.CompanionTheory.IrredMod.exists_finiteDimensional_zalg_lie_stable | exact GlobalTheory.CompanionTheory.IrredMod.exists_finiteDimensional_zalg_lie_stable | (intros; apply GlobalTheory.CompanionTheory.IrredMod.exists_finiteDimensional_zalg_lie_stable <;> assumption)
