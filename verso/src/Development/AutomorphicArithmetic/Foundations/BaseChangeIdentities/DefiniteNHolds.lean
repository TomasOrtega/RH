import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FillPre
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.FrameEx
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowSwap

/- English proof (translation)
The claim follows from `UpperTheory.BaseChangeIdentities.baseChangeN_of UpperTheory.HeckeLevelFrameExistence.candFin`.
-/
theorem UpperTheory.BaseChangeIdentities.baseChangeN : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  UpperTheory.BaseChangeIdentities.baseChangeN_of UpperTheory.HeckeLevelFrameExistence.candFin
