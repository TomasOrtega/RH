import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaSelfAdjointLieOfCountLimitDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnitLemmaSelfAdjointLieOfCountLimitDescent.lean&line=137#L137)
-/
theorem _root_.GlobalTheory.T.unitLemmaSelfAdjointLie_of_count_limit_descent : CountIdentity → UnitaryLimit → LinearDescent → UnitLemmaLie := by
  first | exact @GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of | exact GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of | (intros; apply GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of <;> assumption)
