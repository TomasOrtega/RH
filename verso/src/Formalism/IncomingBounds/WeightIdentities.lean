import Formalism.IncomingBounds.FlowDegreeBounds.MaxFlowValueAttained
import Formalism.IncomingBounds.FlowDegreeBounds.LemmaF
import Formalism.IncomingBounds.FlowDegreeBounds.LemmaFd
import Formalism.IncomingBounds.FlowDegreeBounds.BaseTermLeTopTerm
import Formalism.IncomingBounds.FlowDegreeBounds.PadicValFactorialRatioProd
import Formalism.IncomingBounds.FlowDegreeBounds.AltChooseSumEqZero
import Formalism.IncomingBounds.FlowDegreeBounds.IndexLastReductionHolds
import Formalism.IncomingBounds.FlowDegreeBounds.Cayley
import Formalism.IncomingBounds.FlowDegreeBounds.Series
import Formalism.IncomingBounds.FlowDegreeBounds.ProdRangeEqFactorialMulProdIco

namespace Formalism.IncomingBounds

/- English proof (translation)
The claim follows from `constantIdentities`.
-/
theorem constants : Constants := constantIdentities
/- English proof (translation)
The claim follows from `padicValuationGain`.
-/
theorem valGain : ValGain := padicValuationGain
/- English proof (translation)
The claim follows from `maxFlowValueAttained`.
-/
theorem flowAttained : FlowAttained := maxFlowValueAttained
/- English proof (translation)
The claim follows from `strongDuality`.
-/
theorem lemmaFa : LemmaFa := strongDuality
/- English proof (translation)
The claim follows from `lemmaFb_of maxFlowValueAttained strongDuality`.
-/
theorem lemmaFb : LemmaFb := lemmaFb_of maxFlowValueAttained strongDuality
/- English proof (translation)
The claim follows from `lemmaFc_of maxFlowValueAttained strongDuality`.
-/
theorem lemmaFc : LemmaFc := lemmaFc_of maxFlowValueAttained strongDuality
/- English proof (translation)
The claim follows from `lemmaFd_of maxFlowValueAttained strongDuality`.
-/
theorem lemmaFd : LemmaFd := lemmaFd_of maxFlowValueAttained strongDuality
/- English proof (translation)
The claim follows from `deficitOfBoundedRatio`.
-/
theorem lemmaFe : LemmaFe := deficitOfBoundedRatio
/- English proof (translation)
The claim follows from `incomingBound_of maxFlowValueAttained strongDuality`.
-/
theorem incomingBound : IncomingBound := incomingBound_of maxFlowValueAttained strongDuality
/- English proof (translation)
The claim follows from `top_radius_holds`.
-/
theorem topRadius : TopRadius := top_radius_holds
/- English proof (translation)
The claim follows from `corFromThmA_of maxFlowValueAttained strongDuality lemmaFc incomingBound`.
-/
theorem corFromThmA : CorFromThmA :=
  corFromThmA_of maxFlowValueAttained strongDuality lemmaFc incomingBound
/- English proof (translation)
The claim follows from `cayley_hamilton_recursion`.
-/
theorem chRecursion : CHRecursion := cayley_hamilton_recursion
/- English proof (translation)
The claim follows from `cayley_hamilton_value_holds`.
-/
theorem chValue : CHValue := cayley_hamilton_value_holds
/- English proof (translation)
The claim follows from `newton_window_holds`.
-/
theorem newtonWindow : NewtonWindow := newton_window_holds
/- English proof (translation)
The claim follows from `padicValFactorialRatioProd`.
-/
theorem capVal : CapVal := padicValFactorialRatioProd
/- English proof (translation)
The claim follows from `factorialSplit`.
-/
theorem factSplit : FactSplit := factorialSplit
/- English proof (translation)
The claim follows from `weight_identities'`.
-/
theorem weightIdentities : WeightIdentities := weight_identities'
/- English proof (translation)
The claim follows from `contentShift_of maxFlowValueAttained strongDuality lemmaFc incomingBound`.
-/
theorem contentShift : ContentShift :=
  contentShift_of maxFlowValueAttained strongDuality lemmaFc incomingBound
/- English proof (translation)
The claim follows from `highLevelTail`.
-/
theorem levelTail : LevelTail := highLevelTail
/- English proof (translation)
The claim follows from `frobenius_orbit_sum_holds`.
-/
theorem frobOrbitSum : FrobOrbitSum := frobenius_orbit_sum_holds
/- English proof (translation)
The claim follows from `frobenius_orbit_period_holds`.
-/
theorem frobOrbitPeriod : FrobOrbitPeriod := frobenius_orbit_period_holds
/- English proof (translation)
The claim follows from `index_last_reduction_holds`.
-/
theorem indexLastStep : IndexLastStep := index_last_reduction_holds
/- English proof (translation)
The claim follows from `cayleyIdentity`.
-/
theorem cayleyId : CayleyId := cayleyIdentity
/- English proof (translation)
The claim follows from `sqSubOneInvMulDvd`.
-/
theorem invWeight : InvWeight := sqSubOneInvMulDvd
/- English proof (translation)
The claim follows from `primeDvdChooseIff`.
-/
theorem binomGcd : BinomGcd := primeDvdChooseIff
/- English proof (translation)
The claim follows from `padicValFactorialBounds`.
-/
theorem factValBounds : FactValBounds := padicValFactorialBounds
/- English proof (translation)
The claim follows from `unitFactorialProd`.
-/
theorem uProduct : UProduct := unitFactorialProd
/- English proof (translation)
The claim follows from `logCoeffValuation`.
-/
theorem logCoeffVal : LogCoeffVal := logCoeffValuation
/- English proof (translation)
The claim follows from `shiftExponentIdentity`.
-/
theorem lemmaMExponent : LemmaMExponent := shiftExponentIdentity
/- English proof (translation)
The claim follows from `weightNumerics`.
-/
theorem lemmaMNumerics : LemmaMNumerics := weightNumerics

end Formalism.IncomingBounds
