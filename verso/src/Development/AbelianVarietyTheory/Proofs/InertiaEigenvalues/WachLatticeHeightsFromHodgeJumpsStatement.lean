import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumps
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWachLatticeHeightsFromHodgeJumps.lean&line=382#L382)
-/
theorem _root_.GlobalTheory.T.wachLattice_heights_from_hodgeJumps : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), P5 D HW F := by
  first | exact @GlobalTheory.NL.Heights.heights_from_jumps | exact GlobalTheory.NL.Heights.heights_from_jumps | (intros; apply GlobalTheory.NL.Heights.heights_from_jumps <;> assumption)
