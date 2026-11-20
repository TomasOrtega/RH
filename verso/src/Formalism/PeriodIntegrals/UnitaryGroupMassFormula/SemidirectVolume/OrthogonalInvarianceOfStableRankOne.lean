import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.BVRApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.GlGeneratedTransvectionsDiag
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.UniHaar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TraceGramNondegenerate
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.HasStableRangeOne

namespace PI.VolSemiDirect.W.Cj

/- English proof (translation)
The claim follows from `orthInv_of h1 gl_generated_transvections_diag transvection_preserves_haar`.
-/
theorem orthogonal_invariance_of_stable_rank_one (h1 : AdeleStableRankOne) : OrthInv :=
  orthInv_of h1 gl_generated_transvections_diag transvection_preserves_haar

/- English proof (translation)
The claim follows from `vMod_of (orthogonal_invariance_of_stable_rank_one h1) trace_basis_holds trace_gram_nondegenerate`.
-/
theorem unipotent_modulus_of_stable_rank_one (h1 : AdeleStableRankOne) : VMod :=
  vMod_of (orthogonal_invariance_of_stable_rank_one h1) trace_basis_holds trace_gram_nondegenerate

/- English proof (translation)
The claim follows from `unipotent_modulus_of_stable_rank_one PI.VolSemiDirect.W.SR.stable_rank_one_adeles`.
-/
theorem unipotent_modulus_holds : VMod := unipotent_modulus_of_stable_rank_one PI.VolSemiDirect.W.SR.stable_rank_one_adeles

end PI.VolSemiDirect.W.Cj
