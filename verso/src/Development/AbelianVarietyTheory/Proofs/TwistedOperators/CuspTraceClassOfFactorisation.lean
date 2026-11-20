import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspDiscreteDecompositionOfDecay
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspidalModerateGrowthRapidDecayStatement

namespace GlobalTheory.Published

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem cuspTraceClass_of_factorisation : DixmierMalliavinFactorisation → CuspTraceClass :=
  fun h => cuspTraceClass_of_decay GlobalTheory.T.cuspidal_moderateGrowth_rapidDecay h

end GlobalTheory.Published
