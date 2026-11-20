import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ComplexMultiplicationJacquetShalikaStatement

namespace GlobalTheory.CompanionTheory.CM

/- English proof (translation)
The claim follows from `GlobalTheory.Published.ComplexMultiplicationJSt.oneOrbit GlobalTheory.T.complex_multiplication_jacquet_shalika`.
-/
theorem idealInvariantsOneOrbit : GlobalTheory.Published.IdealInvariantsOneOrbitSt :=
  GlobalTheory.Published.ComplexMultiplicationJSt.oneOrbit GlobalTheory.T.complex_multiplication_jacquet_shalika

end GlobalTheory.CompanionTheory.CM
