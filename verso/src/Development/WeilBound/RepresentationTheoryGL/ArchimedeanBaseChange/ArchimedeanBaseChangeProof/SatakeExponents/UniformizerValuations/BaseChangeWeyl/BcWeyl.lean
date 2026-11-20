import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SatIndepOf

noncomputable section

namespace PositivityTheory.Rg.BcB.F.LemB

/- English proof (translation)
Introduce `_ _ _ h` and use `GlobalTheory.LGrp.bcParam_of_weylConj h`.
-/
theorem bcWeyl : BcWeyl := fun _ _ _ h => GlobalTheory.LGrp.bcParam_of_weylConj h

end PositivityTheory.Rg.BcB.F.LemB

end
