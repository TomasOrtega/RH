import Formalism.CMTypeGalois.CMTypeFrobenius.MQGalois
import Formalism.CMTypeGalois.CMTypeFrobenius.MQKummer
import Formalism.CMTypeGalois.CMTypeFrobenius.MQFrob
import Formalism.CMTypeGalois.CMTypeFrobenius.KroneckerMeaning
import Formalism.CMTypeGalois.CMTypeFrobenius.TypesA
import Formalism.CMTypeGalois.CMTypeFrobenius.TypesB
import Mathlib
import Formalism.CMTypeGalois.CMTypeFrobenius.HostFrob
import Formalism.CMTypeGalois.CMTypeFrobenius.HostConj
import Formalism.CMTypeGalois.CMTypeFrobenius.HostInertia
import Formalism.CMTypeGalois.CMTypeFrobenius.HostMu
import Formalism.CMTypeGalois.CMTypeFrobenius.HostEmb

open NumberField Ideal

namespace Formalism.Q3

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mqKummer : MQKummer := mqKummer_of mqGalois
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mqFrob : MQFrob := mqFrob_of mqGalois
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hostGalois : HostGalois := hostGalois_of mqGalois mqKummer
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hostFrob : HostFrob := hostFrob_of mqFrob hostGalois kroneckerMeaning
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hostConj : HostConj := hostConj_of hostGalois mqKummer
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hostInertia : HostInertia := hostInertia_of hostGalois mqGalois
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hostMu : HostMu := hostMu_of mqKummer hostGalois
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hostEmb : HostEmb := hostEmb_of hostConj hostGalois

end Formalism.Q3
