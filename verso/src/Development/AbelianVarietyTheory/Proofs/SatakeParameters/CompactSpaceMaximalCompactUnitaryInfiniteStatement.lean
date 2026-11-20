import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompactSpaceMaximalCompactUnitaryInfinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
open GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KinfCompactness.compactSpace_Kinf` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FCompactSpaceMaximalCompactUnitaryInfinite.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.compactSpace_maximalCompact_unitary_infinite : ∀ (E : Type) [Field E] (a : ℕ), CompactSpace (Kinf E a) := by
  first | exact @GlobalTheory.KinfCompactness.compactSpace_Kinf | exact GlobalTheory.KinfCompactness.compactSpace_Kinf | (intros; apply GlobalTheory.KinfCompactness.compactSpace_Kinf <;> assumption)
