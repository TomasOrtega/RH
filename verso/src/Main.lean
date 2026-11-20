import Statements
import Supplements.Kernels.MainTheoremsAll

/- English proof (authored)
Apply the reduction from right half-plane nonvanishing for Dirichlet L-functions to the Riemann Hypothesis. The nonvanishing theorem for every character supplies its hypothesis.
-/
theorem riemannHypothesis : RiemannHypothesis := rhOfAll

/- English proof (authored)
Let s be a zero of the zeta function distinct from 1 and from the negative even integers. The Riemann Hypothesis established above applies to precisely these zeros and gives real part 1/2.
-/
theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll

/- English proof (authored)
Fix a Dirichlet character and a point strictly to the right of the critical line. The assumption on the character or the point excludes the exceptional pair of the principal character and s = 1, so the right half-plane nonvanishing theorem applies.
-/
theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi

/- English proof (authored)
Fix a character and a zero in the open critical strip. The critical-strip conclusion of the combined nonvanishing theorem applies to all characters and forces real part 1/2.
-/
theorem LFunction_eq_zero_re : DirichletLZerosOnLine := claimAll.2.1

/- English proof (authored)
Apply the critical-line theorem for primitive characters to the given zero in the open critical strip. It gives Re(s) = 1/2.
-/
theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := critAll
