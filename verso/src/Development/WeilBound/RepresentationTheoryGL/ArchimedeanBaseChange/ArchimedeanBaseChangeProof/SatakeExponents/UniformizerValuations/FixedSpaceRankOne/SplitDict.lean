import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitDictionaryHoldsStatement

namespace PositivityTheory.Rg.BcB.F.Eig.CSD

open PositivityTheory.Rg.BcB.F.Eig

/- English proof (translation)
The claim follows from `GlobalTheory.T.split_dictionary_holds`.
-/
theorem splitDict : SplitDict := GlobalTheory.T.split_dictionary_holds

end PositivityTheory.Rg.BcB.F.Eig.CSD
