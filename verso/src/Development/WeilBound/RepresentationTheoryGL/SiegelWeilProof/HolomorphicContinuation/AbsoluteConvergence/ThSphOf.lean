import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphC
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ThSphB

namespace PositivityTheory.Rg.Sw.AbsSt

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem thSph_of : KAK → Mult → DerivativeVacuumDilations → Sph → SecZero → HolParam → LC → NullIff → ThSph :=
  fun hKAK hMult hD hSph hSZ hHP hLC _ => thSph_of' helpA helpC hKAK hMult hD hSph hSZ hHP hLC

end PositivityTheory.Rg.Sw.AbsSt
