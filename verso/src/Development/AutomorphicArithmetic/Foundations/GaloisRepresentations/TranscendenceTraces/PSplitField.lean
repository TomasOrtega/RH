import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SplittingFieldConstruction
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.SplittingFieldConstruction.splitField_of`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.splitField_of :
    SplitField :=
  _root_.UpperTheory.Reformulated.B.SplittingFieldConstruction.splitField_of
