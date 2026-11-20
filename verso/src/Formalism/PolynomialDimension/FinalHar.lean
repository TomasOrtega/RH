import Formalism.PolynomialDimension.MultinomialDepth.PairingAdjointLaplacianHolds
import Formalism.PolynomialDimension.MultinomialDepth.HarmonicDecompositionHolds
import Formalism.PolynomialDimension.MultinomialDepth.DiagLaplacianDivPowMemSqrtFockLattice
import Formalism.PolynomialDimension.MultinomialDepth.SqrtFockGaussLatticeComparisonHolds

namespace Formalism.CountingSumsFrames.Top

/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.slTwoCommutator_holds`.
-/
theorem slTwo : Formalism.CountingSumsFrames.SlTwo := Formalism.CountingSumsFrames.slTwoCommutator_holds
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.harmonicProjection_holds`.
-/
theorem harProj : Formalism.CountingSumsFrames.HarProj := Formalism.CountingSumsFrames.harmonicProjection_holds
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.isotypicProjection_holds`.
-/
theorem levelProj : Formalism.CountingSumsFrames.LevelProj := Formalism.CountingSumsFrames.isotypicProjection_holds
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.gaussLatticeProjection_holds`.
-/
theorem gaussProj : Formalism.CountingSumsFrames.GaussProj := Formalism.CountingSumsFrames.gaussLatticeProjection_holds
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.gaussLemmaPairing_holds`.
-/
theorem gaussLemmaH : Formalism.CountingSumsFrames.GaussLemmaH := Formalism.CountingSumsFrames.gaussLemmaPairing_holds
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.isotypicLattice_holds`.
-/
theorem levelLattice : Formalism.CountingSumsFrames.LevelLattice := Formalism.CountingSumsFrames.isotypicLattice_holds
/- English proof (translation)
The claim follows from `Formalism.CountingSumsFrames.harmonicQuotient_holds`.
-/
theorem harQuot : Formalism.CountingSumsFrames.HarQuot := Formalism.CountingSumsFrames.harmonicQuotient_holds

end Formalism.CountingSumsFrames.Top
