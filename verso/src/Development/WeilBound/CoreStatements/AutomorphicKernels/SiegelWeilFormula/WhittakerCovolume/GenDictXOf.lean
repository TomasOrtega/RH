import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IwaRedOfC
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.PureGenSubFock
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.LinRedC
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.CoreX
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.GramZeroLeft
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.VacIsPureBy
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.DictAsm
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThGramIncM
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasHermTop
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Height
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.RelExOf

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

/- English proof (translation)
The claim follows from `dictAsmX cellFormula relEx Ht.heightDict measDict thetaDict`.
-/
theorem genDictX_of : GenDictX :=
  dictAsmX cellFormula relEx Ht.heightDict measDict thetaDict

/- English proof (translation)
The claim follows from `whitK_of_X iwaRedC pureSpan linRedC coreX genDictX_of kFinK hT hA hR hF hK hS hU hW hTC hLB hPK`.
-/
theorem whitK_of (hT : TAll) (hA : AuxiliaryPrimeFunction) (hR : RDEx) (hF : FockMem) (hK : KFinPoly) (hS : SecK) (hU : Unfold) (hW : Gen.WhitGenLt)
    (hTC : ThetaCoef) (hLB : LamBd) (hPK : PolyKFin) : WhitK :=
  whitK_of_X iwaRedC pureSpan linRedC coreX genDictX_of kFinK hT hA hR hF hK hS hU hW hTC hLB hPK

/- English proof (translation)
The claim follows from `whitEq_of_X iwaRedC pureSpan linRedC coreX genDictX_of kFinK hT hA hR hF hK hS hU hEW hW hTC hLB hPK`.
-/
theorem whitEq_of (hT : TAll) (hA : AuxiliaryPrimeFunction) (hR : RDEx) (hF : FockMem) (hK : KFinPoly) (hS : SecK) (hU : Unfold) (hEW : EisWk)
    (hW : Gen.WhitGenEq) (hTC : ThetaCoef) (hLB : LamBd) (hPK : PolyKFin) : WhitEq :=
  whitEq_of_X iwaRedC pureSpan linRedC coreX genDictX_of kFinK hT hA hR hF hK hS hU hEW hW hTC hLB hPK

/- English proof (translation)
The claim follows from `whitLow_of_X iwaRedC vacSpan linRedC coreX genDictX_of hVK hT hA hF hS hU hEW hW hTC hLB hPK`.
-/
theorem whitLow_of (hVK : VacK)
    (hT : TAll) (hA : AuxiliaryPrimeFunction) (hF : FockMem) (hS : SecK) (hU : Unfold) (hEW : EisWk) (hW : Gen.WhitGenLow)
    (hTC : ThetaCoef) (hLB : LamBd) (hPK : PolyKFin) : WhitLow :=
  whitLow_of_X iwaRedC vacSpan linRedC coreX genDictX_of hVK hT hA hF hS hU hEW hW hTC hLB hPK

end PositivityTheory.SiegelWeilFormula.KWhit

end
