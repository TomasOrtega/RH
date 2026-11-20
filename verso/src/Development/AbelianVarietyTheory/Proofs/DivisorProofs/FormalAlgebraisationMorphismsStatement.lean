import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormalAlgebraisationMorphisms.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.formalAlgebraisation_morphisms' : GlobalTheory.Published.FormalAlgebraisation.Morphisms := by
  first | exact @GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms | exact GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms | (intros; apply GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms <;> assumption)
