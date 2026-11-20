import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.ReadSplitOfJoin
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.OfEqOfLocComp

namespace PositivityTheory.Rg.BcB.F.RS

/- English proof (translation)
The claim follows from `JB.joinMod_holds`.
-/
theorem join_module_holds : JoinMod := JB.joinMod_holds

/- English proof (translation)
The claim follows from `readMod_of join_module_holds`.
-/
theorem reading_module_holds : ReadMod := readMod_of join_module_holds

/- English proof (translation)
The claim follows from `readSplit_of_join join_module_holds`.
-/
theorem reading_split_holds : ReadSplit := readSplit_of_join join_module_holds

end PositivityTheory.Rg.BcB.F.RS
