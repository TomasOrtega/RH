import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphismsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraisationProperFormalSchemeAmpleBundleStatement

namespace GlobalTheory

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem formalAlgebraisation : GlobalTheory.Published.FormalAlgebraisation :=
  ⟨GlobalTheory.T.formalAlgebraisation_morphisms', GlobalTheory.T.algebraisation_properFormalScheme_ampleBundle⟩

end GlobalTheory
