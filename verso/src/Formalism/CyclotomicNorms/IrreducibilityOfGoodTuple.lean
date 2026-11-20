import Formalism.CyclotomicNorms.NonsquarefreeBounds.Newton
import Formalism.CyclotomicNorms.NonsquarefreeBounds.SubstitutionBound
import Formalism.CyclotomicNorms.NonsquarefreeBounds.SpanQuadraticOfImage
import Formalism.CyclotomicNorms.NonsquarefreeBounds.Central
import Formalism.CyclotomicNorms.NonsquarefreeBounds.Cycles
import Formalism.TameInertiaTowers.FinalGroup
import Formalism.CyclotomicNorms.NonsquarefreeBounds.Jordan
import Formalism.CyclotomicNorms.NonsquarefreeBounds.RestrictionOfBlocksAndJordan
import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds
import Formalism.CyclotomicNorms.NonsquarefreeBounds.IrreducibilityOfRestriction

namespace Formalism.CyclotomicNorms

/- English proof (translation)
The claim follows from `evaluation_bound`.
-/
theorem evaluation : Evaluation := evaluation_bound
/- English proof (translation)
The claim follows from `central_scalar_holds`.
-/
theorem centralScalar : CentralScalar := central_scalar_holds

/- English proof (translation)
The claim follows from `restriction_of_blocks_and_jordan blocks_form_cycle jordan_transitivity`.
-/
theorem restriction : Restriction := restriction_of_blocks_and_jordan blocks_form_cycle jordan_transitivity

/- English proof (translation)
The claim follows from `irreducibility_of_restriction restriction`.
-/
theorem irreducibility_of_good_tuple : IrreducibilityCriterion := irreducibility_of_restriction restriction

end Formalism.CyclotomicNorms
