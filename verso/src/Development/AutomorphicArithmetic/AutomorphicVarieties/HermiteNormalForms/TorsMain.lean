import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TorsBoundPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Assembly

/- English proof (translation)
The claim follows from `UpperTheory.V.KT.torsBoundPow`.
-/
theorem UpperTheory.V.KT.torsMain :
    ∃ C : ℝ, UpperTheory.V.K.TorsBoundPow C :=
  UpperTheory.V.KT.torsBoundPow
