import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraisationProperFormalSchemeAmpleBundle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAlgebraisationProperFormalSchemeAmpleBundle.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.algebraisation_properFormalScheme_ampleBundle : GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  first | exact @GlobalTheory.FormalAlg.formalAlgebraisation_schemes | exact GlobalTheory.FormalAlg.formalAlgebraisation_schemes | (intros; apply GlobalTheory.FormalAlg.formalAlgebraisation_schemes <;> assumption)
