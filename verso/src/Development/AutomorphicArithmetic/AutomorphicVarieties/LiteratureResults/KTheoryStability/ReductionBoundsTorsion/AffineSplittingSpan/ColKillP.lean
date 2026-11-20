import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.E2VanishingOtherColumnsOfColKillP
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.AevalSlice

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem colKillP : ColKillP := fun _ _ _ _ pr s hs u hu q f hf _ x hx hv => colKill pr s hs u hu q f hf x hx hv

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem e2z : E2VanishingFirstColumn := e2VanishingFirstColumn_of_colKillP colKillP

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem e2s : E2VanishingOtherColumns := e2VanishingOtherColumns_of_colKillP colKillP

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
