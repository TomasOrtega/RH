import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHighestWeightVectorOfKStable
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ExistsHW.exists_highestWeight` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsHighestWeightVectorOfKStable.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.exists_highestWeight_vector_of_KStable : ∀ (p q : ℕ) (M : GKMod p q) (W : Submodule ℂ M.V), FiniteDimensional ℂ W → KStable M.act W → W ≠ ⊥ → ∃ (μ : Ix p q → ℚ) (v : M.V), v ∈ W ∧ IsHW M.act μ v := by
  first | exact @GlobalTheory.ExistsHW.exists_highestWeight | exact GlobalTheory.ExistsHW.exists_highestWeight | (intros; apply GlobalTheory.ExistsHW.exists_highestWeight <;> assumption)
