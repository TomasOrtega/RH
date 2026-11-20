import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHCModuleOfGradedDenseGK
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GradedKFin.isHCMod_of_graded` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIsHCModuleOfGradedDenseGK.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.isHCModule_of_graded_dense_gK : ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), Function.Injective j → Dense (Set.range j) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → ∀ (N : ℕ → Submodule ℂ M.V) (k : T.G) (lam : ℕ → ℂ), (∀ m, FiniteDimensional ℂ (N m)) → (⨆ m, N m) = ⊤ → k ∈ T.Kset → Function.Injective lam → (∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x) → IsHCMod σ M j := by
  first | exact @GlobalTheory.GradedKFin.isHCMod_of_graded | exact GlobalTheory.GradedKFin.isHCMod_of_graded | (intros; apply GlobalTheory.GradedKFin.isHCMod_of_graded <;> assumption)
