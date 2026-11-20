import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIwasawaCosetSurjOfLeviElementExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertZeta.cosetSurj_of_leviExists` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FUnitaryIwasawaCosetSurjOfLeviElementExists.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.unitaryIwasawaCosetSurj_of_leviElementExists : LeviExists → CosetSurj := by
  first | exact @GlobalTheory.InertZeta.cosetSurj_of_leviExists | exact GlobalTheory.InertZeta.cosetSurj_of_leviExists | (intros; apply GlobalTheory.InertZeta.cosetSurj_of_leviExists <;> assumption)
