import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeGroupCohomologyStrictlyHenselianStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem laurentPolynomial_cohomology_strictlyHenselian_vanishing : GlobalTheory.EtC.C5 := fun q _ A _ hA hq n i => GlobalTheory.T.multiplicativeGroup_cohomology_strictlyHenselian q A hA hq n i

end GlobalTheory.EtC
