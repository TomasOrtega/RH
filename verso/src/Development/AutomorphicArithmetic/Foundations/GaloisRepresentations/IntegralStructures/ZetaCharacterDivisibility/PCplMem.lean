import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.StConj

open NumberField IsDedekindDomain

namespace UpperTheory.Gal.Int.Div

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem cplMem_of : CplMem := by
  intro E _ _ _ w y y' hy
  exact (GlobalTheory.Mem.Chr.conjPl_iff_mem (GlobalTheory.SplitPts.conjE E) (cpl w) w).1
    (GlobalTheory.CuspRep.conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) w) y y' hy

end UpperTheory.Gal.Int.Div
