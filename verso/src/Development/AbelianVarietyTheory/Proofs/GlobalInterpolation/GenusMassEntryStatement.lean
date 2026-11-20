import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GenusMassEntry
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Fc.row_hTu_cTmin` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FGenusMassEntry.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.genus_mass_entry : (∀ D, MassRatioUnderVolume D) → (∀ D, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassAt D 2) → ∀ (Q : V4.Slot) (Lk : LkT Bundle), Row Q Lk fun 𝒜 _ => R1.H_hTu (fun _ y => Formalism.MainNotions.StandardLattice.HarishChandraReduction.cTmin y) 𝒜 := by
  first | exact @GlobalTheory.Fc.row_hTu_cTmin | exact GlobalTheory.Fc.row_hTu_cTmin | (intros; apply GlobalTheory.Fc.row_hTu_cTmin <;> assumption)
