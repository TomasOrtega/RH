import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilations
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousGramX
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GroupPart

namespace PositivityTheory.Rg.Sw.AbsSt

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem derivative_vacuum_section : DerivativeVacuumDilations := DF.derivative_vacuum_of_parts DF.gaussPart DF.groupPart

end PositivityTheory.Rg.Sw.AbsSt
