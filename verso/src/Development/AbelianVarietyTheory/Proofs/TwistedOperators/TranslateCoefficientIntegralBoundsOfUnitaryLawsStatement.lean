import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateCoefficientIntegralBoundsOfUnitaryLaws
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FTranslateCoefficientIntegralBoundsOfUnitaryLaws.lean&line=286#L286)
-/
theorem _root_.GlobalTheory.T.translateCoefficientIntegralBounds_of_unitary_laws : EmbLaws → Boost → PowInt → DecPow → IntBounds := by
  first | exact @GlobalTheory.SepReal.intBounds_main | exact GlobalTheory.SepReal.intBounds_main | (intros; apply GlobalTheory.SepReal.intBounds_main <;> assumption)
