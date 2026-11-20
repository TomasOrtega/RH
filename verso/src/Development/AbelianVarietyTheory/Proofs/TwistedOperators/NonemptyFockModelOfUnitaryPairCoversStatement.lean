import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyFockModelOfUnitaryPairCovers
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FNonemptyFockModelOfUnitaryPairCovers.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.nonempty_fockModel_of_unitary_pair_covers : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s), Nonempty (FockData T0 T1 T2) := by
  first | exact @GlobalTheory.nonempty_fockData_of_covers | exact GlobalTheory.nonempty_fockData_of_covers | (intros; apply GlobalTheory.nonempty_fockData_of_covers <;> assumption)
