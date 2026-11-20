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

/- English proof (authored)
The region bound follows from the local zero expansion, the polynomial growth and reciprocal bounds, and the right-half-plane estimate for the logarithmic derivative.
-/
theorem logDerivRegionChi : LogDerivRegionChi :=
  log_deriv_in_zero_free_region landau_local3 lfunction_polynomial_growth inverseBound l_log_deriv_right

/- English proof (authored)
Use the character Perron formula and the rectangular residue identity in the smoothing theorem. The logarithmic derivative bounds in the zero-free region and to the right of one supply its contour estimates.
-/
theorem smoothChi : SmoothChi :=
  smoothed_character_sum_of perron_formula_character rectangle_contour_shift_character logDerivRegionChi l_log_deriv_right

/- English proof (authored)
Apply the passage from the smoothed formula to the character Chebyshev estimate, using the smoothed character bound for nonprincipal characters and the prime number theorem for the principal case.
-/
theorem psiChiBound : PsiChiBound :=
  chebyshev_character_bound_of smoothChi Formalism.ZF.gzPNT

/- English proof (authored)
Combine the assumed Siegel lower bound for values at one with the derivative bound near one. The exceptional-zero theorem turns these into a lower bound on the distance of a real zero from one.
-/
theorem excBound_of_siegelLower (hS : SiegelLower) : ExcBound :=
  exceptional_zero_bound_of hS lfunction_deriv_near_one

/- English proof (authored)
The assumed lower bound supplies the exceptional-zero distance estimate. Use it with the character Chebyshev estimate and the zero-free region to obtain the stated Siegel–Walfisz bound.
-/
theorem siegelWalfisz_of_siegelLower (hS : SiegelLower) : SiegelWalfisz :=
  siegel_walfisz_character_of psiChiBound zFRDirichlet (excBound_of_siegelLower hS)

/- English proof (authored)
Apply the exceptional-zero implication to the established Siegel lower bound.
-/
theorem excBound : ExcBound := excBound_of_siegelLower siegelLower

/- English proof (authored)
Apply the Siegel–Walfisz implication to the established Siegel lower bound.
-/
theorem siegelWalfisz : SiegelWalfisz := siegelWalfisz_of_siegelLower siegelLower

end Formalism.ZeroFreeDirichlet
