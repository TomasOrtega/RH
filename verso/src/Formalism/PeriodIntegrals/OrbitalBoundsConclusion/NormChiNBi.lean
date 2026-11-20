import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterNormMatrixInverse.FmatMulInv

/- English proof (translation)
The claim follows from `PIW.NormChiNBi.chiNBi_holds X`.
-/
theorem chi_n_bilinear {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Formalism.L2.SG.NormCut.ChiNBi X :=
  PIW.NormChiNBi.chiNBi_holds X
