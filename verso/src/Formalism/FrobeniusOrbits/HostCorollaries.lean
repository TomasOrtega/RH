import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ConjReal
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrderOfSignGroupDvdTwo
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardExtendedGaloisGroup
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Orbits
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickOrbit
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickFrames
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ExistsOpenNormalOrderOf
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrdUnimod
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.NcardEqTwoIff
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.OrbitSg
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickExists
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.EqZeroOfNegEq
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum

namespace Formalism.FrobeniusOrbits.Final

open Formalism.FrobeniusOrbits

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem conj : HostConj := hostConj_of hostGalois hostGalSpec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem real : HostReal := hostReal_of hostGalois hostGalSpec conj
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem f1 : TwoPowerCyclotomicLayerRealSubfieldCharacterization := real_subfield_of_galois_spec hostGalSpec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cmType : HostCMType := hostCMType_of hostGalois hostGalSpec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frob : HostFrob := hostFrob_of hostGalois hostGalSpec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem splitK : HostSplitK := hostSplitK_of (hostFrob_of hostGalois hostGalSpec)
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem efgTwo : HostEFGTwo := hostEFGTwo_of hostInertia hostDecomp
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ramified : HostRamified := hostRamified_of hostInertia

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem host_field :
    HostExample ∧ HostGroup ∧ HostOrders ∧ HostRecip ∧ HostFixed ∧ HostGalois ∧ HostGalSpec ∧
    HostConj ∧ HostReal ∧ TwoPowerCyclotomicLayerRealSubfieldCharacterization ∧ HostMu ∧ HostFrob ∧ HostInertia ∧ HostUnramEF ∧
    HostDecomp ∧ HostDecompConj ∧ HostEFGTwo ∧ HostSplitK ∧ HostCMType :=
  ⟨hostExample, hostGroup, hostOrders, hostRecip, hostFixed, hostGalois, hostGalSpec, conj, real, f1, hostMu,
    frob, hostInertia, hostUnramEF, hostDecomp, hostDecompConj, efgTwo, splitK, cmType⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem host_places :
    HostThickOrbit ∧ HostThickExists ∧ HostTops ∧ HostProG ∧ HostStab ∧ HostOrdinary ∧ HostUnimodular ∧
    HostConductor ∧ HostEta ∧ HostOrbitCountSg :=
  ⟨hostThickOrbit, hostThickExists, hostTops, hostProG, hostStab, hostOrdinary, hostUnimodular,
    hostConductor, hostEta, hostOrbitCountSg⟩

end Formalism.FrobeniusOrbits.Final
