import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.AutomorphicFormsLeSm

/- English proof (translation)
Introduce `_ _ _ _ _ φ h` and use `(UpperTheory.V.Cm.isCuspForm_iff φ).1 h`.
-/
theorem UpperTheory.V.KernelIndexFullLattice.brCusp_holds :
    UpperTheory.V.KernelIndexFullLattice.BrCusp :=
  fun _ _ _ _ _ φ h => (UpperTheory.V.Cm.isCuspForm_iff φ).1 h
