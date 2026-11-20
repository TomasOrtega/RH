import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FillPre
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.FrameEx
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowSwap

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem UpperTheory.BaseChangeIdentities.baseChangeN : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  UpperTheory.BaseChangeIdentities.baseChangeN_of UpperTheory.HeckeLevelFrameExistence.candFin
