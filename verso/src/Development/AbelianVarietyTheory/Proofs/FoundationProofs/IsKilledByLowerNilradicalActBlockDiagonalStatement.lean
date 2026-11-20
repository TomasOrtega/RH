import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKilledByLowerNilradicalActBlockDiagonal
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KilledByLowerStable.killedByLower_act` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIsKilledByLowerNilradicalActBlockDiagonal.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.isKilledByLowerNilradical_act_blockDiagonal : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ Z : Mat p q, IsKC Z → ∀ x : V, KilledByLower act x → KilledByLower act (act Z x) := by
  first | exact @GlobalTheory.KilledByLowerStable.killedByLower_act | exact GlobalTheory.KilledByLowerStable.killedByLower_act | (intros; apply GlobalTheory.KilledByLowerStable.killedByLower_act <;> assumption)
