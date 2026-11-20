import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockSumSemisimple
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isSS_blockSum_of_isIrred` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBlockSumSemisimple.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.block_sum_semisimple : ∀ {k Γ : Type} [Field k] [Group Γ] {r t : ℕ} (ρ : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → (Γ →* kˣ)), GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsIrred (matRep ρ) → IsSS (GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum ρ χ) := by
  first | exact @GlobalTheory.isSS_blockSum_of_isIrred | exact GlobalTheory.isSS_blockSum_of_isIrred | (intros; apply GlobalTheory.isSS_blockSum_of_isIrred <;> assumption)
