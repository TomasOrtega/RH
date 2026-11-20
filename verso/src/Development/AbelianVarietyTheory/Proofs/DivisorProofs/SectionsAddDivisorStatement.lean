import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsAddDivisor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Cartier.SecAdd.sections_add` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSectionsAddDivisor.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.sections_add_divisor : ∀ (X : Scheme.{0}) [IsIntegral X] [IsAffine X] (D E : CartierDiv X),
    (D + E).sections = D.sections * E.sections := by
  first | exact @GlobalTheory.Cartier.SecAdd.sections_add | exact GlobalTheory.Cartier.SecAdd.sections_add | (intros; apply GlobalTheory.Cartier.SecAdd.sections_add <;> assumption)
