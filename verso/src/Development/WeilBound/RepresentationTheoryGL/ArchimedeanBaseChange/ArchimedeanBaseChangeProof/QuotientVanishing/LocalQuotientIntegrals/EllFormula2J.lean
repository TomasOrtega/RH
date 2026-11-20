import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.ClassVanish
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotIntegralZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscreteTopologyProdMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsQuotNormaliserIndicator

namespace PositivityTheory.Rg.BcB.CV

open PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.D4

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem classVanish2 : ClassVanish2 := classVanish2_of (GlobalTheory.CompanionTheory.SliceFubini.sliceTerm_of mahler) classVanish sizeBasic

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ellFormula2J : EllFormula2J := ellFormula2_of (GlobalTheory.CompanionTheory.TwUnfold.unfold2_of mahler) ellTerm classVanish2 sizeBasic

end PositivityTheory.Rg.BcB.CV
