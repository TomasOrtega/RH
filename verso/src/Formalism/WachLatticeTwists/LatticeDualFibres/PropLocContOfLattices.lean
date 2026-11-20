import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.PropLoc
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ConnTors
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.HOneTorsionFree
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ExistsPowSmulIntegral
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ExistsBasisOfLattice

universe u

namespace Formalism.RepresentationBoundsCohomology.LOC

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem propLocCont_of_lattices (hEmb : StatQuotEmbeds.{u}) (hDual : StatDualLattice.{u}) :
    StatPropLocCont.{u} := propLocCont_of connTors hEmb hDual

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem propLocCont : StatPropLocCont.{u} := propLocCont_of_lattices quotEmbeds dualLattice

end Formalism.RepresentationBoundsCohomology.LOC
