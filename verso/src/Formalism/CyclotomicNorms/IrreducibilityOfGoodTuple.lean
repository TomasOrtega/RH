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
A detailed English derivation is pending.
-/
theorem evaluation : Evaluation := evaluation_bound
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem centralScalar : CentralScalar := central_scalar_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem restriction : Restriction := restriction_of_blocks_and_jordan blocks_form_cycle jordan_transitivity

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem irreducibility_of_good_tuple : IrreducibilityCriterion := irreducibility_of_restriction restriction

end Formalism.CyclotomicNorms
