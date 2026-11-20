import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.LieOperatorConjHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.VectorComplexifiedDerivativeCommutator
import Formalism.RealPlaceAnalysis.IsRightTranslationIsometric
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactArrFiniteDimensional
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero

namespace Formalism.REAL
/- English proof (translation)
The claim follows from `compact_haar_holds`.
-/
theorem kHaar : KHaar := compact_haar_holds
/- English proof (translation)
The claim follows from `compact_exponential_surjective`.
-/
theorem kExp : KExp := compact_exponential_surjective
/- English proof (translation)
The claim follows from `genExp_of kExp`.
-/
theorem genExp : GenExp := genExp_of kExp
/- English proof (translation)
The claim follows from `vector_right_derivative_extends`.
-/
theorem rdExtV : RdExtV := vector_right_derivative_extends
/- English proof (translation)
The claim follows from `vector_right_derivative_left_invariant`.
-/
theorem rdLeftV : RdLeftV := vector_right_derivative_left_invariant
/- English proof (translation)
The claim follows from `rdSmoothV_of rdExtV`.
-/
theorem rdSmoothV : RdSmoothV := rdSmoothV_of rdExtV
/- English proof (translation)
The claim follows from `rdLinV_of rdExtV`.
-/
theorem rdLinV : RdLinV := rdLinV_of rdExtV
/- English proof (translation)
The claim follows from `rdBracketV_of rdExtV rdSmoothV`.
-/
theorem rdBracketV : RdBracketV := rdBracketV_of rdExtV rdSmoothV
/- English proof (translation)
The claim follows from `eabGlV_of rdLinV rdBracketV rdSmoothV`.
-/
theorem eabGlV : EabGlV := eabGlV_of rdLinV rdBracketV rdSmoothV
/- English proof (translation)
The claim follows from `rdVPair_of rdExtV`.
-/
theorem rdVPair : RdVPair := rdVPair_of rdExtV
/- English proof (translation)
The claim follows from `ecSumV_of rdLinV`.
-/
theorem ecSumV : EcSumV := ecSumV_of rdLinV
/- English proof (translation)
The claim follows from `compact_weight_orthogonal`.
-/
theorem kWtOrth : KWtOrth := compact_weight_orthogonal
/- English proof (translation)
The claim follows from `compact_lowering_holds`.
-/
theorem kLow : KLow := compact_lowering_holds
/- English proof (translation)
The claim follows from `compact_casimir_span_holds`.
-/
theorem kCasSpan : KCasSpan := compact_casimir_span_holds
/- English proof (translation)
The claim follows from `kOrth_of kLow kWtOrth`.
-/
theorem kOrth : KOrth := kOrth_of kLow kWtOrth
/- English proof (translation)
The claim follows from `kHiUniq_of kLow kWtOrth kOrth`.
-/
theorem kHiUniq : KHiUniq := kHiUniq_of kLow kWtOrth kOrth
/- English proof (translation)
The claim follows from `highestWeightExists_holds`.
-/
theorem kHiExist : KHiExist := highestWeightExists_holds
/- English proof (translation)
The claim follows from `kIrr_of kHiExist kHiUniq`.
-/
theorem kIrr : KIrr := kIrr_of kHiExist kHiUniq
/- English proof (translation)
The claim follows from `kDecomp_of kHiExist kOrth`.
-/
theorem kDecomp : KDecomp := kDecomp_of kHiExist kOrth
/- English proof (translation)
The claim follows from `kIsoSplit_of kDecomp kOrth`.
-/
theorem kIsoSplit : KIsoSplit := kIsoSplit_of kDecomp kOrth
/- English proof (translation)
The claim follows from `kWtBound_of kCasSpan`.
-/
theorem kWtBound : KWtBound := kWtBound_of kCasSpan
/- English proof (translation)
The claim follows from `kCasBound_of kDecomp kCasSpan kOrth`.
-/
theorem kCasBound : KCasBound := kCasBound_of kDecomp kCasSpan kOrth
/- English proof (translation)
The claim follows from `casimir_on_cyclic_holds`.
-/
theorem casOnCyc : CasOnCyc := casimir_on_cyclic_holds
/- English proof (translation)
The claim follows from `pfil_facts_hold`.
-/
theorem pfilFacts : PfilFacts := pfil_facts_hold
/- English proof (translation)
The claim follows from `arr_module_facts`.
-/
theorem arrModule : ArrModule := arr_module_facts
/- English proof (translation)
The claim follows from `theta_filtration_holds`.
-/
theorem thetaFil : ThetaFil := theta_filtration_holds
/- English proof (translation)
The claim follows from `hVCoeff_of kLow kWtOrth arrModule`.
-/
theorem hVCoeff : HVCoeff := hVCoeff_of kLow kWtOrth arrModule
/- English proof (translation)
The claim follows from `typesSplit_of hVCoeff kIsoSplit arrModule`.
-/
theorem typesSplit : TypesSplit := typesSplit_of hVCoeff kIsoSplit arrModule
/- English proof (translation)
The claim follows from `casArr_of kCasSpan`.
-/
theorem casArr : CasArr := casArr_of kCasSpan
/- English proof (translation)
The claim follows from `symmetricSliceMixedCasimir_holds`.
-/
theorem omSymSlice : OmSymSlice := symmetricSliceMixedCasimir_holds
/- English proof (translation)
The claim follows from `positiveArraysInvariant_holds`.
-/
theorem nStable : NStable := positiveArraysInvariant_holds
/- English proof (translation)
The claim follows from `omPlus_of kDecomp kOrth kCasSpan casArr arrModule`.
-/
theorem omPlus : OmPlus := omPlus_of kDecomp kOrth kCasSpan casArr arrModule
/- English proof (translation)
The claim follows from `nPos_of casArr omSymSlice omPlus`.
-/
theorem nPos : NPos := nPos_of casArr omSymSlice omPlus
end Formalism.REAL
