import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.DiracOfDiracZeroModule
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalMemUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSqLeDominantRearrangement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestTermLemmaReal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.N2TopReal

namespace PositivityTheory.RgBcC.RealD

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.RealCountG.countG`.
-/
theorem countG_holds : CountG := GlobalTheory.CompanionTheory.RealCountG.countG

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.DiracKType0.dirac_inequality_k_types`.
-/
theorem dirac_inequality_k_types : DiracInequalityWithoutSplitComponent := GlobalTheory.CompanionTheory.DiracKType0.dirac_inequality_k_types

/- English proof (translation)
The claim follows from `adm_least_zero_of_dirac GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T dirac_inequality_k_types GlobalTheory.CompanionTheory.SpinBound.lemmaHT`.
-/
theorem adm_least_zero_holds : AdmLeast0 :=
  adm_least_zero_of_dirac GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T dirac_inequality_k_types GlobalTheory.CompanionTheory.SpinBound.lemmaHT

/- English proof (translation)
The claim follows from `adm_least_of_zero_module adm_least_zero_holds`.
-/
theorem adm_least_holds : AdmLeast := adm_least_of_zero_module adm_least_zero_holds

end PositivityTheory.RgBcC.RealD
