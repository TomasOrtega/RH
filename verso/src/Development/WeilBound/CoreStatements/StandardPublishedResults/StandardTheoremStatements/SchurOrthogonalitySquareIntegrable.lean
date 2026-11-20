import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds

namespace PositivityTheory.Stage1.PM

/- English proof (translation)
The claim follows from `GlobalTheory.Published.schurOrthogonalitySquareIntegrable'`.
-/
theorem schurOrthogonalitySquareIntegrable : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable :=
  GlobalTheory.Published.schurOrthogonalitySquareIntegrable'

/- English proof (translation)
The claim follows from `GlobalTheory.Published.HeckeLPartialContinuation_holds`.
-/
theorem heckeLPartialContinuation : GlobalTheory.Published.HeckeLPartialContinuation :=
  GlobalTheory.Published.HeckeLPartialContinuation_holds

/- English proof (translation)
The claim follows from `GlobalTheory.Published.hermitianLocalGlobal_holds`.
-/
theorem hermitianLocalGlobal : GlobalTheory.Published.HermitianLocalGlobal :=
  GlobalTheory.Published.hermitianLocalGlobal_holds

/- English proof (translation)
The claim follows from `GlobalTheory.Published.radfordShufflePolynomial_holds`.
-/
theorem radfordShufflePolynomial : GlobalTheory.Published.RadfordShufflePolynomial :=
  GlobalTheory.Published.radfordShufflePolynomial_holds

end PositivityTheory.Stage1.PM
