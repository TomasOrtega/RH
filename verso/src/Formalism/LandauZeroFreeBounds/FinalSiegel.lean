import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.CharExists
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqCoeff
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqEntire
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqGrowth
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LFunctionOneUpperBound
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqKeyOf
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZetaNegReal
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRealPos
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SameCharacterLFunctionOne
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelOf

namespace Formalism.ZeroFreeDirichlet

/- English proof (authored)
The product has nonnegative Dirichlet coefficients, an entire remainder after removing its pole, and a polynomial growth bound on the Taylor circle. The value-at-one estimate controls the pole coefficient. These are the inputs to the product inequality.
-/
theorem bqKey : BqKey :=
  product_lfunction_key_inequality dirichlet_product_coefficients dirichlet_product_entire product_lfunction_growth_bound lfunction_one_upper_bound

/- English proof (authored)
Apply the Siegel lower-bound theorem with the product-character construction and the explicit nonprincipal real character. The Taylor product inequality, the upper bound at one, and the signs of the real zeta and L-values give its analytic hypotheses. The comparison at one for characters agreeing on common units supplies the remaining case.
-/
theorem siegelLower : SiegelLower :=
  siegel_theorem_of exists_product_character exists_real_nontrivial_character bqKey lfunction_one_upper_bound zeta_negative_real_axis
    real_lfunction_real_on_reals lfunction_one_same_character

end Formalism.ZeroFreeDirichlet
