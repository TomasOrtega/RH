import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf

noncomputable section

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.Pf.Slab

/- English proof (translation)
Introduce `_ X Y u` and use `neatKu_of_gamUnipKu X u Y.hK (latOfLattice_holds X u) (gamUnipKu_holds X u Y.hK)`.
-/
theorem neatKu_full : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X)
    (u : D.what₂.Word), NeatKu X u Y.hK :=
  fun _ X Y u => neatKu_of_gamUnipKu X u Y.hK (latOfLattice_holds X u) (gamUnipKu_holds X u Y.hK)

/- English proof (translation)
The claim follows from `rInvC_of nilradical_conj_level'`.
-/
theorem rInvC_holds : RInvC := rInvC_of nilradical_conj_level'

/- English proof (translation)
The claim follows from `ooLintSumC_of_parts Formalism.L2.SG.Pf.RegroupPf.slabCoverC_holds hMaj rInvC_holds hCnt neatKu_full`.
-/
theorem ooLintSumC_holds_slab (hMaj : MajPtC) (hCnt : CountC) : OOLintSumC :=
  ooLintSumC_of_parts Formalism.L2.SG.Pf.RegroupPf.slabCoverC_holds hMaj rInvC_holds hCnt neatKu_full

end Formalism.L2.SG.Pf
