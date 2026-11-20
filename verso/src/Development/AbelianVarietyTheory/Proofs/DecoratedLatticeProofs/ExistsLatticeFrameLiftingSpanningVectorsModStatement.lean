import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeFrameLiftingSpanningVectorsMod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LiftFrameMod.exists_isLiftFrame` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsLatticeFrameLiftingSpanningVectorsMod.lean&line=218#L218)
-/
theorem _root_.GlobalTheory.T.exists_latticeFrame_lifting_spanning_vectors_mod : ∀ (D : D7) (g : ℕ), g ≠ 0 → ∀ b : ℕ → VA (instOf D), (∀ j, b j ∈ (instOf D).Lf) → (∀ y ∈ (instOf D).Lf, InMod (instOf D) g (Set.range fun j : Fin (instOf D).n => b j.val) y) → ∃ β, IsLiftFrame (instOf D) g b β := by
  first | exact @GlobalTheory.LiftFrameMod.exists_isLiftFrame | exact GlobalTheory.LiftFrameMod.exists_isLiftFrame | (intros; apply GlobalTheory.LiftFrameMod.exists_isLiftFrame <;> assumption)
