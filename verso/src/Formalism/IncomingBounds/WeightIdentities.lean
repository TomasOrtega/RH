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
A detailed English derivation is pending.
-/
theorem constants : Constants := constantIdentities
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem valGain : ValGain := padicValuationGain
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem flowAttained : FlowAttained := maxFlowValueAttained
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemmaFa : LemmaFa := strongDuality
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemmaFb : LemmaFb := lemmaFb_of maxFlowValueAttained strongDuality
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemmaFc : LemmaFc := lemmaFc_of maxFlowValueAttained strongDuality
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemmaFd : LemmaFd := lemmaFd_of maxFlowValueAttained strongDuality
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemmaFe : LemmaFe := deficitOfBoundedRatio
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem incomingBound : IncomingBound := incomingBound_of maxFlowValueAttained strongDuality
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem topRadius : TopRadius := top_radius_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem corFromThmA : CorFromThmA :=
  corFromThmA_of maxFlowValueAttained strongDuality lemmaFc incomingBound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem chRecursion : CHRecursion := cayley_hamilton_recursion
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem chValue : CHValue := cayley_hamilton_value_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem newtonWindow : NewtonWindow := newton_window_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem capVal : CapVal := padicValFactorialRatioProd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem factSplit : FactSplit := factorialSplit
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem weightIdentities : WeightIdentities := weight_identities'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem contentShift : ContentShift :=
  contentShift_of maxFlowValueAttained strongDuality lemmaFc incomingBound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem levelTail : LevelTail := highLevelTail
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frobOrbitSum : FrobOrbitSum := frobenius_orbit_sum_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frobOrbitPeriod : FrobOrbitPeriod := frobenius_orbit_period_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem indexLastStep : IndexLastStep := index_last_reduction_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cayleyId : CayleyId := cayleyIdentity
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem invWeight : InvWeight := sqSubOneInvMulDvd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem binomGcd : BinomGcd := primeDvdChooseIff
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem factValBounds : FactValBounds := padicValFactorialBounds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem uProduct : UProduct := unitFactorialProd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem logCoeffVal : LogCoeffVal := logCoeffValuation
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemmaMExponent : LemmaMExponent := shiftExponentIdentity
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemmaMNumerics : LemmaMNumerics := weightNumerics

end Formalism.IncomingBounds
