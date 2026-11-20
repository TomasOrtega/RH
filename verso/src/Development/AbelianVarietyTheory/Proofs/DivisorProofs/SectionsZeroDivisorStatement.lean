import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsZeroDivisor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSectionsZeroDivisor.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.sections_zero_divisor : ∀ (X : Scheme.{0}) [IsIntegral X], (0 : CartierDiv X).sections = 1 := by
  first | exact @GlobalTheory.Cartier.CartierDiv.sections_zero_eq_one | exact GlobalTheory.Cartier.CartierDiv.sections_zero_eq_one | (intros; apply GlobalTheory.Cartier.CartierDiv.sections_zero_eq_one <;> assumption)
