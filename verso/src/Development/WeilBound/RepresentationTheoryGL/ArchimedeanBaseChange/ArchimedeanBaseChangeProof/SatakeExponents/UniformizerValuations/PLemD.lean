import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PolynomialPairSpaces.InfUniq
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PolynomialPairSpaces.InfPartsHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PolynomialPairSpaces.PairNe

/- English proof (translation)
The claim follows from `PositivityTheory.Rg.BcB.F.LemDd.lemD_of PositivityTheory.Rg.BcB.F.LemDd.InfUniq_holds PositivityTheory.Rg.BcB.F.LemDd.Tw.InfParts_holds PositivityTheory.Rg.BcB.SpectralAccumulation.InfTreeP.infTree_holds`.
-/
theorem PositivityTheory.Rg.BcB.F.LemDd.lemD : PositivityTheory.Rg.BcB.F.LemDd.LemD :=
  PositivityTheory.Rg.BcB.F.LemDd.lemD_of PositivityTheory.Rg.BcB.F.LemDd.InfUniq_holds PositivityTheory.Rg.BcB.F.LemDd.Tw.InfParts_holds
    PositivityTheory.Rg.BcB.SpectralAccumulation.InfTreeP.infTree_holds
