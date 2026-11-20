import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodsOnLineOfInvLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinrankInvFunBranch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodsInvariantFunctionalStatement

open GlobalTheory.RowClaim GlobalTheory.RowReal

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GlobalTheory.RowReal.periodsOnLine_big : Big fun ch => PeriodsOnLine ch :=
  big_mono (fun ch h => periodsOnLine_of_invLine GlobalTheory.OneFunctional.oneLine ch h) GlobalTheory.T.rowTest_definitePeriods_invariant_functional
