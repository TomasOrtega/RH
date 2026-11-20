import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.OfInputs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LiftFactorization.FirstQuadraticSquareHolds
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopStd
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.GenericUnitaryDualGLHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.Crys

namespace UpperTheory.Gal.Int.Inp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem js : GlobalTheory.Published.JacquetShalikaRigidity := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gk : GlobalTheory.Published.GelfandKazhdanDual := UpperTheory.Gal.AbelianGaloisNormality.gk_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem adm : GlobalTheory.Published.IrreducibleAdmissibleGL := UpperTheory.Zero.LLC.Pr.adm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem len : GlobalTheory.Published.StandardFunctorsFiniteLength := PositivityTheory.Tls2.BZGL.standardFunctorsFiniteLength_top
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exh : GlobalTheory.Published.LanglandsExhaustionGL := UpperTheory.Zero.LLC.Pr.exh
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zel : GlobalTheory.Published.ZelevinskyPolynomialRing := UpperTheory.Zero.LLC.Pr.zel
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gen : GlobalTheory.Published.GenericUnitaryDualGL := PositivityTheory.Gud.Fin.genericUnitaryDualGL_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ac : GlobalTheory.Published.ArthurClozelStrongTC := UpperTheory.Gal.AbelianGaloisNormality.strongTC_holds

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem inp_holds : Inp := ⟨js, gk, adm, len, exh, zel, gen, ac, hk, alg, pst⟩

end UpperTheory.Gal.Int.Inp
