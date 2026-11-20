import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilations
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousGramX
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GroupPart

namespace PositivityTheory.Rg.Sw.AbsSt

/- English proof (translation)
The claim follows from `DF.derivative_vacuum_of_parts DF.gaussPart DF.groupPart`.
-/
theorem derivative_vacuum_section : DerivativeVacuumDilations := DF.derivative_vacuum_of_parts DF.gaussPart DF.groupPart

end PositivityTheory.Rg.Sw.AbsSt
