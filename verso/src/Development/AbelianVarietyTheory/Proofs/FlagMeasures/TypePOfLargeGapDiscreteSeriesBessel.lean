import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocDatCOfBesselOfW
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataTailBoundClosedFormLargeGapsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeBoundAtTermsOfLocalDataStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairCountBoundOfSiegelMassRatiosStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAmplitudeFactorNonneg
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeMassRatio

namespace GlobalTheory.TypeAsm.TopGap

/- English proof (translation)
Introduce `hH hBW`. Establish `hAmp : GlobalTheory.TypeAsm.AmpP` using `GlobalTheory.T.amplitudeBound_at_terms_of_localData (GlobalTheory.TypeAsm.locDatC_of_besselOfW hBW) (GlobalTheory.T.localDataTailBound_closedForm_largeGaps hH)`. Establish `hPairs : GlobalTheory.TypeAsm.PairsP` using `GlobalTheory.T.termPairCountBound_of_siegelMassRatios GlobalTheory.Mass.MaxFormula.main GlobalTheory.Mass.siegelMassRatio_holds`. Conclude with `GlobalTheory.TypeAsm.typeBound_of_amplitude_pairs hAmp hPairs`.
-/
theorem typeBound_of_gap :
    GlobalTheory.GapIn.Hyp → Formalism.L2.SG.LocWSOf.BesselOfW → Formalism.L2.SG.RowsPos.TypeP := by
  intro hH hBW

  have hAmp : GlobalTheory.TypeAsm.AmpP :=
    GlobalTheory.T.amplitudeBound_at_terms_of_localData (GlobalTheory.TypeAsm.locDatC_of_besselOfW hBW) (GlobalTheory.T.localDataTailBound_closedForm_largeGaps hH)

  have hPairs : GlobalTheory.TypeAsm.PairsP :=
    GlobalTheory.T.termPairCountBound_of_siegelMassRatios GlobalTheory.Mass.MaxFormula.main GlobalTheory.Mass.siegelMassRatio_holds
  exact GlobalTheory.TypeAsm.typeBound_of_amplitude_pairs hAmp hPairs

end GlobalTheory.TypeAsm.TopGap
