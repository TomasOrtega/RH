import Development.AutomorphicArithmetic.ShortNorms.SmallOneOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesImagQuadShortIntervalLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesInProgressionsRelativeErrorStatement

/- English proof (translation)
The claim follows from `GlobalTheory.T.normPrimesImagQuad_short_interval_lower_bound`.
-/
theorem UpperTheory.T3.shortNorm : UpperTheory.T3.ShortNorm := GlobalTheory.T.normPrimesImagQuad_short_interval_lower_bound

/- English proof (translation)
The claim follows from `UpperTheory.T3.smallOne_of GlobalTheory.T.primesInProgressions_relativeError`.
-/
theorem UpperTheory.T3.smallOne : UpperTheory.T3.SmallOne := UpperTheory.T3.smallOne_of GlobalTheory.T.primesInProgressions_relativeError
