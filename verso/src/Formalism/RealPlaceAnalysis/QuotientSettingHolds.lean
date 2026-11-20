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
A detailed English derivation is pending.
-/
theorem kHaar : KHaar := compact_haar_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kExp : KExp := compact_exponential_surjective
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem genExp : GenExp := genExp_of kExp
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rdExtV : RdExtV := vector_right_derivative_extends
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rdLeftV : RdLeftV := vector_right_derivative_left_invariant
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rdSmoothV : RdSmoothV := rdSmoothV_of rdExtV
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rdLinV : RdLinV := rdLinV_of rdExtV
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rdBracketV : RdBracketV := rdBracketV_of rdExtV rdSmoothV
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eabGlV : EabGlV := eabGlV_of rdLinV rdBracketV rdSmoothV
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rdVPair : RdVPair := rdVPair_of rdExtV
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ecSumV : EcSumV := ecSumV_of rdLinV
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kWtOrth : KWtOrth := compact_weight_orthogonal
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kLow : KLow := compact_lowering_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kCasSpan : KCasSpan := compact_casimir_span_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kOrth : KOrth := kOrth_of kLow kWtOrth
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kHiUniq : KHiUniq := kHiUniq_of kLow kWtOrth kOrth
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kHiExist : KHiExist := highestWeightExists_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kIrr : KIrr := kIrr_of kHiExist kHiUniq
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kDecomp : KDecomp := kDecomp_of kHiExist kOrth
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kIsoSplit : KIsoSplit := kIsoSplit_of kDecomp kOrth
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kWtBound : KWtBound := kWtBound_of kCasSpan
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kCasBound : KCasBound := kCasBound_of kDecomp kCasSpan kOrth
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem casOnCyc : CasOnCyc := casimir_on_cyclic_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pfilFacts : PfilFacts := pfil_facts_hold
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem arrModule : ArrModule := arr_module_facts
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thetaFil : ThetaFil := theta_filtration_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hVCoeff : HVCoeff := hVCoeff_of kLow kWtOrth arrModule
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem typesSplit : TypesSplit := typesSplit_of hVCoeff kIsoSplit arrModule
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem casArr : CasArr := casArr_of kCasSpan
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem omSymSlice : OmSymSlice := symmetricSliceMixedCasimir_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nStable : NStable := positiveArraysInvariant_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem omPlus : OmPlus := omPlus_of kDecomp kOrth kCasSpan casArr arrModule
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nPos : NPos := nPos_of casArr omSymSlice omPlus
end Formalism.REAL
