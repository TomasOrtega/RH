import Mathlib
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.AcrisNAlgebraMapAinf
import Development.WeilBound.CoreStatements.PeriodRingComparison.AinfAlgebraMaps.CAAlgebraMapGOC
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.BcrisPlusHomAlgebraMap

noncomputable section

open GroundTheory.PAdicHodge
open Formalism.BasicNotions.Loc (GQ)

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Establish `key : ((cBc l).toRingHom.comp (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g))).comp (cBc l).symm.toRingHom = Formalism.Per6.σB g` using `PositivityTheory.LocInh.bcris_hom_ext fun y => by`. Express the relevant statement in the definitionally equal form `cBc l (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g) ((cBc l).symm (Formalism.Per6.cB l y))) = _`. Rewrite using `[cBc_symm_cB, Reformulated.AutPerF.Bcris.map_algebraMap_acris (gOC l g) (Reformulated.AutPerF.toRingHom_injective g), cBc_algebraMap, cA_map_gal, RingEquiv.apply_symm_apply, PositivityTheory.LocInh.σB_cB]`. Establish `h` using `RingHom.congr_fun key (cBc l b)`. Express the relevant statement in the definitionally equal form `cBc l (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g) ((cBc l).symm (cBc l b))) = _ at h`.

Rewrite `h` using `[RingEquiv.symm_apply_apply]`. Then use the resulting hypothesis.
-/
theorem cBc_gal (g : GQ l) (b : Reformulated.AutPerF.Bcris l (OC l)) :
    cBc l (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g) b) =
      Formalism.Per6.σB g (cBc l b) := by
  have key : ((cBc l).toRingHom.comp
      (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g))).comp
        (cBc l).symm.toRingHom = Formalism.Per6.σB g :=
    PositivityTheory.LocInh.bcris_hom_ext fun y => by
      change cBc l (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g)
        ((cBc l).symm (Formalism.Per6.cB l y))) = _
      rw [cBc_symm_cB, Reformulated.AutPerF.Bcris.map_algebraMap_acris (gOC l g) (Reformulated.AutPerF.toRingHom_injective g),
        cBc_algebraMap, cA_map_gal,
        RingEquiv.apply_symm_apply, PositivityTheory.LocInh.σB_cB]
  have h := RingHom.congr_fun key (cBc l b)
  change cBc l (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g)
    ((cBc l).symm (cBc l b))) = _ at h
  rwa [RingEquiv.symm_apply_apply] at h

/- English proof (translation)
The claim follows from `cBc_gal l g b`.
-/
theorem cBc_smul (g : GQ l) (b : Reformulated.AutPerF.Bcris l (OC l)) :
    cBc l (g • b) = Formalism.Per6.σB g (cBc l b) :=
  cBc_gal l g b

end Cmp6
