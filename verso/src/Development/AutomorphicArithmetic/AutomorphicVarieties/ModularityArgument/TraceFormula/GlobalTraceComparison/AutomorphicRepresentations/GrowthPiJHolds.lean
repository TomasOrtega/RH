import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PThetaInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.LdetRatMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.ZeroPf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.KerRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PGBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.WeakPf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPointRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PartEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SuppPf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PEvalBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PFinGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PFinFac
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PDropP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.GFacPf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PositionPairFunctionsEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PRangeW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.FlipHalf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTrFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PSizes
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PInCut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PDomInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PHalfTerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTailInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PDiagInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PUncutOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTailOf
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.RGrowthJ
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.EllFormula2J

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

/- English proof (translation)
The claim follows from `aeEq_pf basic_pf`.
-/
theorem aeEq : AeEq := aeEq_pf basic_pf
/- English proof (translation)
The claim follows from `zero_pf aeEq`.
-/
theorem zero : Zero := zero_pf aeEq
/- English proof (translation)
The claim follows from `pointRep_pf aeEq kInv_pf`.
-/
theorem pointRep : PointRep := pointRep_pf aeEq kInv_pf
/- English proof (translation)
The claim follows from `ker_pf weak_pf pointRep pComm_pf pDiag_pf`.
-/
theorem ker : Ker := ker_pf weak_pf pointRep pComm_pf pDiag_pf
/- English proof (translation)
The claim follows from `supp_pf basic_pf zero kInv_pf pSupp_pf ker`.
-/
theorem supp : Supp := supp_pf basic_pf zero kInv_pf pSupp_pf ker
/- English proof (translation)
The claim follows from `gBound_pf basic_pf`.
-/
theorem gBound : GBound := gBound_pf basic_pf
/- English proof (translation)
The claim follows from `gFac_pf (finFac_pf basic_pf evalBasis_pf (finGen_pf basic_pf)) (dropP_pf zero kInv_pf basic_pf weak_pf pointRep pComm_pf)`.
-/
theorem gFac : GFac := gFac_pf (finFac_pf basic_pf evalBasis_pf (finGen_pf basic_pf))
  (dropP_pf zero kInv_pf basic_pf weak_pf pointRep pComm_pf)
/- English proof (translation)
The claim follows from `rep_pf basic_pf (thetaInt_pf basic_pf) kInv_pf pDiag_pf ker`.
-/
theorem rep : Rep := rep_pf basic_pf (thetaInt_pf basic_pf) kInv_pf pDiag_pf ker
/- English proof (translation)
Apply the tactic sequence `first | exact sizes_of_basic basic_pf | exact sizes_of_basic`.
-/
theorem sizes : Sizes := by first | exact sizes_of_basic basic_pf | exact sizes_of_basic
/- English proof (translation)
The claim follows from `domInt_pf basic_pf sizes`.
-/
theorem domInt : DomInt := domInt_pf basic_pf sizes
/- English proof (translation)
The claim follows from `halfTerm_pf basic_pf gBound supp rep flip_pf domInt`.
-/
theorem halfTerm : HalfTerm := halfTerm_pf basic_pf gBound supp rep flip_pf domInt
/- English proof (translation)
The claim follows from `uncutOf_pf basic_pf gFac halfTerm (rangeW_pf rep) trFin_pf`.
-/
theorem uncutHalf : DiscreteGroups.T1.G.UncutHalf := uncutOf_pf basic_pf gFac halfTerm (rangeW_pf rep) trFin_pf
/- English proof (translation)
The claim follows from `tailOf_pf basic_pf sizes inCut_pf (tailInt_of_bounds gFac gBound supp domInt) (diagInt_pf gFac halfTerm)`.
-/
theorem cutTail : DiscreteGroups.T1.G.CutTail2 :=
  tailOf_pf basic_pf sizes inCut_pf (tailInt_of_bounds gFac gBound supp domInt) (diagInt_pf gFac halfTerm)

/- English proof (translation)
The claim follows from `DiscreteGroups.T1.G.rGrowthPiJ_of (fun _ _ => uncutHalf) (fun _ _ => cutTail) PositivityTheory.Rg.BcB.CV.ellFormula2J PositivityTheory.Rg.BcB.E1.sFun_holds DiscreteGroups.T1.G.Dcy.piVecEx_holds DiscreteGroups.T1.G.piInv`.
-/
theorem growthPiJ_holds : PositivityTheory.Rg.BcB.Desc.GrowthPiJ :=
  DiscreteGroups.T1.G.rGrowthPiJ_of (fun _ _ => uncutHalf) (fun _ _ => cutTail) PositivityTheory.Rg.BcB.CV.ellFormula2J
    PositivityTheory.Rg.BcB.E1.sFun_holds DiscreteGroups.T1.G.Dcy.piVecEx_holds DiscreteGroups.T1.G.piInv

/- English proof (translation)
The claim follows from `growthPiJ_holds`.
-/
theorem growthPi_holds : PositivityTheory.Rg.BcB.Desc.GrowthPi := growthPiJ_holds

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
