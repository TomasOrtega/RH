import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIwasawaCellsDisjoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FUnitaryIwasawaCellsDisjoint.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.unitary_iwasawa_cells_disjoint : CosetInj := by
  first | exact @GlobalTheory.InertZeta.cosetInj | exact GlobalTheory.InertZeta.cosetInj | (intros; apply GlobalTheory.InertZeta.cosetInj <;> assumption)
