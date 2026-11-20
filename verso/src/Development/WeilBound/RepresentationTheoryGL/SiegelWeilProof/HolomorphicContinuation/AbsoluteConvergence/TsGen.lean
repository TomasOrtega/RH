import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TsGenOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DifferentiableSecondCayleyBlockDilation

namespace PositivityTheory.Rg.Sw.AbsSt

/- English proof (translation)
Introduce `_ hD hK hM hS hDF hH hLC` and use `tsGen_of hD hK hM hS hDF hH hLC tsbFacts`.
-/
theorem tsGen : Iwa → CayleyBlocksInvertible → KAK → Mult → SecZero → DerivativeVacuumDilations → HolParam → LC → TSGen :=
  fun _ hD hK hM hS hDF hH hLC => tsGen_of hD hK hM hS hDF hH hLC tsbFacts

end PositivityTheory.Rg.Sw.AbsSt
