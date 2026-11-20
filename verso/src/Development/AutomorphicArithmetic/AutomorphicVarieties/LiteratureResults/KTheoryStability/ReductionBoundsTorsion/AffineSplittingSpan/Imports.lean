import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreMain
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.CoreSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.ColKillP

namespace PositivityTheory.KB.SplitAffineSpectral

/- English proof (translation)
The claim follows from `NormTraceLemmas.core_of NormTraceLemmas.splitA NormTraceLemmas.splitS NormTraceLemmas.splitB NormTraceLemmas.zInv NormTraceLemmas.e2z NormTraceLemmas.e2s`.
-/
theorem core : Core :=
  NormTraceLemmas.core_of NormTraceLemmas.splitA NormTraceLemmas.splitS NormTraceLemmas.splitB NormTraceLemmas.zInv NormTraceLemmas.e2z NormTraceLemmas.e2s

end PositivityTheory.KB.SplitAffineSpectral
