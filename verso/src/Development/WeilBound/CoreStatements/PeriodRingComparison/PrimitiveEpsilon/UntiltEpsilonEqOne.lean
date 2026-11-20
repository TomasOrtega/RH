import Mathlib
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.GammaEqDpow
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.AcrisNAlgebraMapAinf
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective

noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Rewrite using `[← tiltMap_eq]`. Conclude with `Reformulated.AutPerF.Tilt.untilt_map (e l).toRingHom x`.
-/
theorem untilt_tiltMap (x : Reformulated.AutPerF.Tilt l (OC l)) :
    PreTilt.untilt (Formalism.Per6.tiltMap l x) = e l (PreTilt.untilt x) := by
  rw [← tiltMap_eq]
  exact Reformulated.AutPerF.Tilt.untilt_map (e l).toRingHom x

/- English proof (translation)
Apply `(e l).injective` to reduce the goal to its premises. Rewrite using `[← untilt_tiltMap, PositivityTheory.LocInh.tiltMap_εO, map_one]`. Conclude with `untilt_epsilon`.
-/
theorem untilt_epsilon_eq_one : PreTilt.untilt (PositivityTheory.LocInh.εO l) = (1 : OC l) := by
  apply (e l).injective
  rw [← untilt_tiltMap, PositivityTheory.LocInh.tiltMap_εO, map_one]
  exact untilt_epsilon

def eps0 : Reformulated.AutPerF.tateModule l (OC l) := ⟨PositivityTheory.LocInh.εO l, untilt_epsilon_eq_one l⟩

/- English proof (translation)
The claim follows from `PositivityTheory.LocInh.tiltMap_εO`.
-/
theorem tiltMap_epsilon : Formalism.Per6.tiltMap l (eps0 l).1 = epsilon l := PositivityTheory.LocInh.tiltMap_εO

/- English proof (translation)
Unfold `Reformulated.AutPerF.IsPrimitive`. Introduce `h`. Apply `untilt_frobeniusEquiv_symm_epsilon_ne_one (p := l)` to reduce the goal to its premises. Establish `h1 : Formalism.Per6.tiltMap l ((frobeniusEquiv (Reformulated.AutPerF.Tilt l (OC l)) l).symm (eps0 l).1) = (frobeniusEquiv (PreTilt (NC l) l) l).symm (epsilon l)`. Rewrite using `[RingHom.map_frobeniusEquiv_symm, tiltMap_epsilon]`.

Rewrite using `[← h1, untilt_tiltMap, h, map_one]`.
-/
theorem epsilon_isPrimitive : Reformulated.AutPerF.IsPrimitive (eps0 l) := by
  unfold Reformulated.AutPerF.IsPrimitive
  intro h
  apply untilt_frobeniusEquiv_symm_epsilon_ne_one (p := l)
  have h1 : Formalism.Per6.tiltMap l ((frobeniusEquiv (Reformulated.AutPerF.Tilt l (OC l)) l).symm (eps0 l).1) =
      (frobeniusEquiv (PreTilt (NC l) l) l).symm (epsilon l) := by
    rw [RingHom.map_frobeniusEquiv_symm, tiltMap_epsilon]
  rw [← h1, untilt_tiltMap, h, map_one]

end Cmp6
