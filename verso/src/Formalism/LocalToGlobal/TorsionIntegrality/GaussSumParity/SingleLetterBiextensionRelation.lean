import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.FinalOfNRDense
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.OneLetterGaussEveryOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLogDerivativeUnique

namespace Formalism.L2.Th1.D

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nrDense : NRDense := NRDense_of sqrtKur

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nrcmOfCM4 : Formalism.L2.Th1.CM.CM4 → NRCM := NRCM_of sqrtKur denseOK homothetic_lattice_integral_s2 nrDense

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAEntryFinal : ThmAEntryFinal := ThmAEntryFinal_of' nrcmOfCM4
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGaussFinal : ThmAGaussFinal := ThmAGaussFinal_of' nrcmOfCM4
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneLetterGaussFinal : OneLetterGaussFinal := OneLetterGaussFinal_of' nrcmOfCM4
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernelFinal : KernelFinal := KernelFinal_of' nrcmOfCM4

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAEntryEvery : ThmAEntryEvery := ThmAEntryEvery_of nrcmOfCM4
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thmAGaussEvery : ThmAGaussEvery := ThmAGaussEvery_of nrcmOfCM4
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneLetterGaussEvery : OneLetterGaussEvery := OneLetterGaussEvery_of nrcmOfCM4
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernelEvery : KernelEvery := KernelEvery_of nrcmOfCM4

end Formalism.L2.Th1.D
