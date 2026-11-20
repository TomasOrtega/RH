import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcDiff
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcEqOfPowEqOne

open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

variable {φ : Frame} (H : HostRaw φ)

/- English proof (translation)
The claim follows from `splitK H`.
-/
example (D : HostDer H) : type_of% D.splitK := splitK H
/- English proof (translation)
The claim follows from `ordinary H C`.
-/
example (C : HostCore H) (D : HostDer H) : type_of% D.ordinary := ordinary H C
/- English proof (translation)
The claim follows from `eta H C`.
-/
example (C : HostCore H) (D : HostDer H) : type_of% D.eta := eta H C
/- English proof (translation)
The claim follows from `diffSupport H C`.
-/
example (C : HostCore H) (D : HostDer H) : type_of% D.diffSupport := diffSupport H C
/- English proof (translation)
The claim follows from `principal H C`.
-/
example (C : HostCore H) (D : HostDer H) : type_of% D.principal := principal H C
/- English proof (translation)
The claim follows from `unimodular H`.
-/
example (D : HostDer H) : type_of% D.unimodular := unimodular H
/- English proof (translation)
The claim follows from `discr_sq H C`.
-/
example (C : HostCore H) (D : HostDer H) : type_of% D.discr_sq := discr_sq H C
/- English proof (translation)
The claim follows from `norm_mu H C`.
-/
example (C : HostCore H) (D : HostDer H) : type_of% D.norm_mu := norm_mu H C

end Formalism.HC.Der

end
