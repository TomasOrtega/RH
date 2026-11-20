import Statements
import Supplements.Kernels.MainTheoremsAll

/- English proof (authored)
Apply the reduction from right half-plane nonvanishing for Dirichlet L-functions to the Riemann Hypothesis. The nonvanishing input is `allChi` and the resulting proof is `rhOfAll`.
-/
theorem riemannHypothesis : RiemannHypothesis := rhOfAll

/- English proof (authored)
Let s be a zero of the zeta function distinct from 1 and from the negative even integers. These are the exclusions in `rhOfAll`, which gives real part 1/2.
-/
theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll

/- English proof (authored)
Fix a Dirichlet character and a point strictly to the right of the critical line. The assumption on the character or the point excludes the exceptional pair of the principal character and s = 1. Apply `allChi` to obtain nonvanishing.
-/
theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi

/- English proof (authored)
Apply the critical-strip component of `claimAll`. It applies to every Dirichlet character and forces the real part of a zero in the open strip to be 1/2.
-/
theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1

/- English proof (authored)
Apply `critAll` to the primitive character and the zero in the open critical strip. Its conclusion is that the real part of the zero is 1/2.
-/
theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
