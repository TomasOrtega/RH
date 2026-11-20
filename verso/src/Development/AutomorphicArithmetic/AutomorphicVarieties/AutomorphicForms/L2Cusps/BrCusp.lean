import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.AutomorphicFormsLeSm

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem UpperTheory.V.KernelIndexFullLattice.brCusp_holds :
    UpperTheory.V.KernelIndexFullLattice.BrCusp :=
  fun _ _ _ _ _ φ h => (UpperTheory.V.Cm.isCuspForm_iff φ).1 h
