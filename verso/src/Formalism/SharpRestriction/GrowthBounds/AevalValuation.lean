import Formalism.SharpRestriction.GrowthBounds.AevalValuation.MemSupportedOf
import Formalism.SharpRestriction.GrowthBounds.AevalValuation.ValGen
import Formalism.SharpRestriction.GrowthBounds.MonomialSupport.PhMonomialMul
import Formalism.SharpRestriction.GrowthBounds.MonomialSupport.GeZSum
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients

namespace Formalism.MainNotions.TraceSpectra

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem restChain : Formalism.MainNotions.PairMembershipBlocks.RestChain :=
  restChain_of valAeval valFilt Formalism.MainNotions.LetterSubstitution.valNN Formalism.MainNotions.LetterSubstitution.phMon Formalism.MainNotions.LetterSubstitution.compPh Formalism.MainNotions.LetterSubstitution.fdigPh
    Formalism.MainNotions.LetterSubstitution.fdigSum

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stmtE (D : Formalism.BasicNotions.D7) : tableLineDegreeFive.ClosedFormOfAdmitted D := Formalism.MainNotions.PairMembershipBlocks.stmtE_of_chain D restChain

end Formalism.MainNotions.TraceSpectra
