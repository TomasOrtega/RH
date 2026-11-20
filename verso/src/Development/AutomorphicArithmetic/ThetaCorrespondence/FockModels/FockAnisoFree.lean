import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.FockAnisoOfRanges
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.IntegralUnitCoefficients.CoefND
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilDoubledSpaceOfStandardUnitary
import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.WeilSiegelFormula
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SiegelFormulaSchwartz.SiegelFormulaThetaOfSchwartz
import Development.AutomorphicArithmetic.ThetaCorrespondence.WeilRepresentation.WeilTheta

namespace UpperTheory.Lit.Sw47

/- English proof (translation)
The claim follows from `GlobalTheory.StdUnn.sw_doubled_of_std PositivityTheory.SiegelWeilCoefficients.field`.
-/
theorem convergent : GlobalTheory.Published.SiegelWeilUnitaryConvergent := GlobalTheory.StdUnn.sw_doubled_of_std PositivityTheory.SiegelWeilCoefficients.field

/- English proof (translation)
The claim follows from `PositivityTheory.SiegelWeilFormulaUnitary.weilSiegelFormulaUnitary_of_two UpperTheory.Lit.weilThetaConvergence PositivityTheory.Rg.Wsf.weilSiegelFormula`.
-/
theorem weilUnitary : GlobalTheory.Published.WeilSiegelFormulaUnitary :=
  PositivityTheory.SiegelWeilFormulaUnitary.weilSiegelFormulaUnitary_of_two UpperTheory.Lit.weilThetaConvergence PositivityTheory.Rg.Wsf.weilSiegelFormula

/- English proof (translation)
The claim follows from `fa_of convergent weilUnitary`.
-/
theorem fa : FA := fa_of convergent weilUnitary

/- English proof (translation)
The claim follows from `fa D`.
-/
theorem fockAniso_free (_ : GlobalTheory.Published.SiegelWeilAnisotropicUnitary) (D : Formalism.BasicNotions.D7) :
    GlobalTheory.BottomRallis.SiegelWeilFockAniso D := fa D

/- English proof (translation)
Both sides reduce to the same expression.
-/
example : type_of% @fockAniso_free = type_of% @GlobalTheory.BottomRallis.siegelWeilFockAniso_of_siegelWeilAnisotropic := rfl

end UpperTheory.Lit.Sw47
