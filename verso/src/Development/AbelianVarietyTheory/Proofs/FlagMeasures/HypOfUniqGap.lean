import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import CompanionTheory.AutomorphicTheory.PieriRules.InfinitesimalCharacterDiscreteSeries
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanGapSmall
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsFD

namespace GlobalTheory.GapIn

/- English proof (translation)
Introduce `h` and use `⟨CompanionTheory.PieriExpansion.hypsG_of_zuck CompanionTheory.Zuck.zuckerman_gap, h, Formalism.L2.SG.OwnFacts.factMultOne.out, Formalism.L2.SG.OwnFacts.FD.factDsigHC.out⟩`.
-/
theorem hyp_of_uniqGap : GlobalTheory.GapIn.UniqGap → GlobalTheory.GapIn.Hyp :=
  fun h => ⟨CompanionTheory.PieriExpansion.hypsG_of_zuck CompanionTheory.Zuck.zuckerman_gap, h, Formalism.L2.SG.OwnFacts.factMultOne.out,
    Formalism.L2.SG.OwnFacts.FD.factDsigHC.out⟩

end GlobalTheory.GapIn
