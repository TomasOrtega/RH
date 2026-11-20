import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactCoverUnHcModuleFiniteDimIrreducible
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompactCoverIrr.hcMod_finite_irr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCompactCoverUnHcModuleFiniteDimIrreducible.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.compactCoverUn_hcModule_finiteDim_irreducible : ∀ (n : ℕ), 1 ≤ n → ∀ (T : GrpData n 0) (τ : URep T) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H), IrrU τ → IsHCMod τ M j → Nontrivial M.V → FiniteDimensional ℂ M.V ∧ IrrGK M ∧ (∀ h v, ∃ v', j v' = τ.π h (j v)) ∧ ∀ N : Submodule ℂ M.V, (∀ h, ∀ v ∈ N, ∀ v', j v' = τ.π h (j v) → v' ∈ N) → N = ⊥ ∨ N = ⊤ := by
  first | exact @GlobalTheory.CompactCoverIrr.hcMod_finite_irr | exact GlobalTheory.CompactCoverIrr.hcMod_finite_irr | (intros; apply GlobalTheory.CompactCoverIrr.hcMod_finite_irr <;> assumption)
