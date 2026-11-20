import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumOfVacuaIsVacuumBoth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FLastSeeSawDatumOfVacuaIsVacuumBoth.lean&line=200#L200)
-/
theorem _root_.GlobalTheory.T.lastSeeSawDatum_of_vacua_is_vacuum_both : ∀ D : D7, GlobalTheory.FinPl.LastVac D := by
  first | exact @GlobalTheory.LastVacPf.lastVac | exact GlobalTheory.LastVacPf.lastVac | (intros; apply GlobalTheory.LastVacPf.lastVac <;> assumption)
