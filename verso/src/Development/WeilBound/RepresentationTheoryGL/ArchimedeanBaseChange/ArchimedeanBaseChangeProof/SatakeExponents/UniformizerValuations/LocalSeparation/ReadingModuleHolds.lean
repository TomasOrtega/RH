import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.ReadSplitOfJoin
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.OfEqOfLocComp

namespace PositivityTheory.Rg.BcB.F.RS

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem join_module_holds : JoinMod := JB.joinMod_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem reading_module_holds : ReadMod := readMod_of join_module_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem reading_split_holds : ReadSplit := readSplit_of_join join_module_holds

end PositivityTheory.Rg.BcB.F.RS
