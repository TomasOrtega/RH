import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthTransversalFlagsInfIsotropicEqBot
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FOrthTransversalFlagsInfIsotropicEqBot.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.orth_transversal_flags_inf_isotropic_eq_bot : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T'), Submodule.IsLattice E Λ → IsLift Λ F → IsLift Λ F' → Gval F F' ≠ 0 → Hp Λ F F' ≤ orth S (Xplus F) ∧ Hp Λ F F' ≤ orth S (Xplus F') ∧ Hp Λ F F' ⊓ Xsp F = ⊥ := by
  first | exact @GlobalTheory.LoopC.PerpFlags.main | exact GlobalTheory.LoopC.PerpFlags.main | (intros; apply GlobalTheory.LoopC.PerpFlags.main <;> assumption)
