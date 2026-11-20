import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.GaussElementarySymmetric
import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TheoremCIiiMulti
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ABArith
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.FinsuppStepInduction
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.MinorProdBlockDegree
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.NormNatCastLeOfDvd
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EDecomp
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.NormLeOfDvd
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EntryAOneParity
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EntryATwoAndB
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EJoint
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.MPlaces
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.PlacesAddClass
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.KOneConsequenceOf
import Formalism.GrowthSums.FactorialBaseGrowth.PathBasisOfCount

namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7

/- English proof (translation)
The claim follows from `iterate_statement`.
-/
theorem iterate : Iterate := iterate_statement

/- English proof (translation)
The claim follows from `e_one_identity_of`.
-/
theorem e_one_identity : JetPairingHasseIdentity := e_one_identity_of
/- English proof (translation)
The claim follows from `e_one_integral_of`.
-/
theorem e_one_integral : HasseDerivIntegralHomogeneous := e_one_integral_of
/- English proof (translation)
The claim follows from `e_one_vanish_of`.
-/
theorem e_one_vanish : HasseDerivProdVanish := e_one_vanish_of
/- English proof (translation)
The claim follows from `minor_hits`.
-/
theorem minorHits : MinorHits := minor_hits
/- English proof (translation)
The claim follows from `gainFactorialInequality`.
-/
theorem starArith : StarArith := gainFactorialInequality
/- English proof (translation)
The claim follows from `cyclicShiftLeast`.
-/
theorem chargeLemma : ChargeLemma := cyclicShiftLeast
/- English proof (translation)
The claim follows from `excessGainBound`.
-/
theorem entry_a_one_bound : ExcessGainBound := excessGainBound
/- English proof (translation)
The claim follows from `cappedGainBound`.
-/
theorem bCore : BCore := cappedGainBound
/- English proof (translation)
The claim follows from `HitsCapPos_of e_one_vanish minorHits`.
-/
theorem hitsCapPos : HitsCapPos := HitsCapPos_of e_one_vanish minorHits
/- English proof (translation)
The claim follows from `HitsColumnsPos_of e_one_vanish minorHits`.
-/
theorem hitsColumnsPos : HitsColumnsPos := HitsColumnsPos_of e_one_vanish minorHits
/- English proof (translation)
The claim follows from `hasseDerivSupport`.
-/
theorem hasseDegree : HasseDegree := hasseDerivSupport
/- English proof (translation)
The claim follows from `minorProdBlockDegree`.
-/
theorem minorProdDegree : MinorProdDegree := minorProdBlockDegree
/- English proof (translation)
The claim follows from `TermBound_of e_one_identity e_one_integral`.
-/
theorem termBound : TermBound := TermBound_of e_one_identity e_one_integral
/- English proof (translation)
The claim follows from `decomposition_of_hh`.
-/
theorem hhDecomp : HhDecomp := decomposition_of_hh
/- English proof (translation)
The claim follows from `EntryStar_of termBound hhDecomp classSubst Formalism.DworkPowerSeriesWeights.jet_pair_linearity starArith hasseDegree minorProdDegree`.
-/
theorem entryStar : EntryStar :=
  EntryStar_of termBound hhDecomp classSubst Formalism.DworkPowerSeriesWeights.jet_pair_linearity starArith hasseDegree
    minorProdDegree

/- English proof (translation)
The claim follows from `entryExcessBound_of entryStar hitsCapPos entry_a_one_bound chargeLemma`.
-/
theorem entry_a_one : EntryExcessBound := entryExcessBound_of entryStar hitsCapPos entry_a_one_bound chargeLemma
/- English proof (translation)
The claim follows from `entryCappedBound_of entryStar hitsCapPos Formalism.GrowthSums.cappedGainSubLE`.
-/
theorem entry_a_two : EntryCappedBound := entryCappedBound_of entryStar hitsCapPos Formalism.GrowthSums.cappedGainSubLE
/- English proof (translation)
The claim follows from `EntryB_of entryStar hitsCapPos hitsColumnsPos bCore`.
-/
theorem entryB : EntryB := EntryB_of entryStar hitsCapPos hitsColumnsPos bCore

end Formalism.InvariantFactorPaths.G7.Top
