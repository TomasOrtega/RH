import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraisationProperFormalSchemeAmpleBundle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.FormalAlg.formalAlgebraisation_schemes | exact GlobalTheory.FormalAlg.formalAlgebraisation_schemes | (intros; apply GlobalTheory.FormalAlg.formalAlgebraisation_schemes <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.algebraisation_properFormalScheme_ampleBundle : GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  first | exact @GlobalTheory.FormalAlg.formalAlgebraisation_schemes | exact GlobalTheory.FormalAlg.formalAlgebraisation_schemes | (intros; apply GlobalTheory.FormalAlg.formalAlgebraisation_schemes <;> assumption)
