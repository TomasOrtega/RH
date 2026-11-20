import Formalism.LandauZeroFreeBounds.NoZeroComplex
import Formalism.LandauZeroFreeBounds.FinalSiegel
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LandauLocal3
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronChi
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RectShiftChi
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LogDerivRegionChiOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SmoothChiOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PsiChiBoundOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LDerivNearOne
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExcBoundOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelWalfiszOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelWalfiszAPOf
import Formalism.ZeroFreeRegion.LogDerivRegion

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem logDerivRegionChi : LogDerivRegionChi :=
  log_deriv_in_zero_free_region landau_local3 lfunction_polynomial_growth inverseBound l_log_deriv_right

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem smoothChi : SmoothChi :=
  smoothed_character_sum_of perron_formula_character rectangle_contour_shift_character logDerivRegionChi l_log_deriv_right

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem psiChiBound : PsiChiBound :=
  chebyshev_character_bound_of smoothChi Formalism.ZF.gzPNT

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem excBound_of_siegelLower (hS : SiegelLower) : ExcBound :=
  exceptional_zero_bound_of hS lfunction_deriv_near_one

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem siegelWalfisz_of_siegelLower (hS : SiegelLower) : SiegelWalfisz :=
  siegel_walfisz_character_of psiChiBound zFRDirichlet (excBound_of_siegelLower hS)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem excBound : ExcBound := excBound_of_siegelLower siegelLower

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem siegelWalfisz : SiegelWalfisz := siegelWalfisz_of_siegelLower siegelLower

end Formalism.ZeroFreeDirichlet
