import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateCoefficientDerivativeIntegralBoundsOfLa
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SepReal.DerInt.derBounds_of` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FTranslateCoefficientDerivativeIntegralBoundsOfLa.lean&line=225#L225)
-/
theorem _root_.GlobalTheory.T.translateCoefficientDerivativeIntegralBounds_of_laws : EmbLaws → PowInt → DecPow → LieBound → DerBounds := by
  first | exact @GlobalTheory.SepReal.DerInt.derBounds_of | exact GlobalTheory.SepReal.DerInt.derBounds_of | (intros; apply GlobalTheory.SepReal.DerInt.derBounds_of <;> assumption)
