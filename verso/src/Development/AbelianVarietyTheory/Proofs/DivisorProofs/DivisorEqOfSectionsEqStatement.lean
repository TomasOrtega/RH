import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorEqOfSectionsEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Cartier.CartierDiv.eq_of_sections_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDivisorEqOfSectionsEq.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.divisor_eq_of_sections_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsAffine X] (D E : CartierDiv X),
    D.sections = E.sections → D = E := by
  first | exact @GlobalTheory.Cartier.CartierDiv.eq_of_sections_eq | exact GlobalTheory.Cartier.CartierDiv.eq_of_sections_eq | (intros; apply GlobalTheory.Cartier.CartierDiv.eq_of_sections_eq <;> assumption)
