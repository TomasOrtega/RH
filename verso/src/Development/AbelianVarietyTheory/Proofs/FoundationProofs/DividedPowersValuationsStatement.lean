import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DividedPowersValuations
import Formalism.PairingDivisors.StatementN
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.legendre_divided_powers` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FDividedPowersValuations.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.divided_powers_valuations : Formalism.PairingDivisionLocalBalance.DivPow := by
  first | exact @GlobalTheory.legendre_divided_powers | exact GlobalTheory.legendre_divided_powers | (intros; apply GlobalTheory.legendre_divided_powers <;> assumption)
