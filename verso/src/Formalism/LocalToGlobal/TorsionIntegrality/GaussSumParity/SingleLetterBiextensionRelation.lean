import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.FinalOfNRDense
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.OneLetterGaussEveryOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLogDerivativeUnique

namespace Formalism.L2.Th1.D

/- English proof (translation)
The claim follows from `NRDense_of sqrtKur`.
-/
theorem nrDense : NRDense := NRDense_of sqrtKur

/- English proof (translation)
The claim follows from `NRCM_of sqrtKur denseOK homothetic_lattice_integral_s2 nrDense`.
-/
theorem nrcmOfCM4 : Formalism.L2.Th1.CM.CM4 → NRCM := NRCM_of sqrtKur denseOK homothetic_lattice_integral_s2 nrDense

/- English proof (translation)
The claim follows from `ThmAEntryFinal_of' nrcmOfCM4`.
-/
theorem thmAEntryFinal : ThmAEntryFinal := ThmAEntryFinal_of' nrcmOfCM4
/- English proof (translation)
The claim follows from `ThmAGaussFinal_of' nrcmOfCM4`.
-/
theorem thmAGaussFinal : ThmAGaussFinal := ThmAGaussFinal_of' nrcmOfCM4
/- English proof (translation)
The claim follows from `OneLetterGaussFinal_of' nrcmOfCM4`.
-/
theorem oneLetterGaussFinal : OneLetterGaussFinal := OneLetterGaussFinal_of' nrcmOfCM4
/- English proof (translation)
The claim follows from `KernelFinal_of' nrcmOfCM4`.
-/
theorem kernelFinal : KernelFinal := KernelFinal_of' nrcmOfCM4

/- English proof (translation)
The claim follows from `ThmAEntryEvery_of nrcmOfCM4`.
-/
theorem thmAEntryEvery : ThmAEntryEvery := ThmAEntryEvery_of nrcmOfCM4
/- English proof (translation)
The claim follows from `ThmAGaussEvery_of nrcmOfCM4`.
-/
theorem thmAGaussEvery : ThmAGaussEvery := ThmAGaussEvery_of nrcmOfCM4
/- English proof (translation)
The claim follows from `OneLetterGaussEvery_of nrcmOfCM4`.
-/
theorem oneLetterGaussEvery : OneLetterGaussEvery := OneLetterGaussEvery_of nrcmOfCM4
/- English proof (translation)
The claim follows from `KernelEvery_of nrcmOfCM4`.
-/
theorem kernelEvery : KernelEvery := KernelEvery_of nrcmOfCM4

end Formalism.L2.Th1.D
