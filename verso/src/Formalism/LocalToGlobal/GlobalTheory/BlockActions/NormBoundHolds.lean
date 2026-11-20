import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundOfInjectiveStable
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.SymmetricClausesOfFormsNorm

namespace Formalism.L2.GlobalTheoryTheory.Br

/- English proof (translation)
The claim follows from `norm_bound_of_injective_stable class_injective_holds stabiliser_bijective_holds`.
-/
theorem norm_bound_holds : NormBoundAtInfinity := norm_bound_of_injective_stable class_injective_holds stabiliser_bijective_holds

end Formalism.L2.GlobalTheoryTheory.Br
