import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittUnram
import Formalism.PeriodIntegrals.WittUnram
import Formalism.SharpRestriction.GrowthBounds.ObjBridge

namespace Formalism.MainNotions.G.WittPI

/- English proof (translation)
Introduce `p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS` and use `H p n' W Qq σ hS.frac_alt hS.p_unif hS.res_card hS.eq_sum_herm_smul_frame_of_inW hS.frob`.
-/
theorem wittIdent_of (H : PI.WittUnram) : Formalism.MainNotions.G.WittIdent :=
  fun p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS =>
    H p n' W Qq σ hS.frac_alt hS.p_unif hS.res_card hS.eq_sum_herm_smul_frame_of_inW hS.frob

/- English proof (translation)
The claim follows from `wittIdent_of witt_unramified`.
-/
theorem wittIdentity_holds : Formalism.MainNotions.G.WittIdent := wittIdent_of witt_unramified

end Formalism.MainNotions.G.WittPI
