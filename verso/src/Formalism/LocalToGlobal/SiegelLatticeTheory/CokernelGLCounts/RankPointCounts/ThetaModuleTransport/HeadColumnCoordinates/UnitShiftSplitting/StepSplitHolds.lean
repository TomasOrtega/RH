import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondProjUniformizerMul
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.FormSplit

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

/- English proof (translation)
The claim follows from `gamSplit_of gamSub_holds gamSup_holds`.
-/
theorem gamSplit_holds : GamSplitP := gamSplit_of gamSub_holds gamSup_holds

/- English proof (translation)
The claim follows from `stepSplit_of gamSplit_holds formSplit_holds`.
-/
theorem stepSplit_holds : Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork.StepSplit := stepSplit_of gamSplit_holds formSplit_holds

end Formalism.L2.SG.LocalCountModules.AlgGSplit
