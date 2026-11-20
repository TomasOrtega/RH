import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsPrincipalDivisor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSectionsPrincipalDivisor.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.sections_principal_divisor : ∀ (X : Scheme.{0}) [IsIntegral X] (g : X.functionFieldˣ),
    (principal g).sections = Submodule.span Γ(X, ⊤) {(g : X.functionField)⁻¹} := by
  first | exact @GlobalTheory.sections_principal | exact GlobalTheory.sections_principal | (intros; apply GlobalTheory.sections_principal <;> assumption)
