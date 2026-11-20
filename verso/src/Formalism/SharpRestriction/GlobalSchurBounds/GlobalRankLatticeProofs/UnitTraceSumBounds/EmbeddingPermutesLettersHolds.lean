import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EmbeddingPermutesLetters
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EmbPerm
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharExtend
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EmbTraceSum

namespace Formalism.MainNotions.Ext

/- English proof (translation)
The claim follows from `embedding_permutation`.
-/
theorem permEmb_holds : PermEmb := embedding_permutation

/- English proof (translation)
The claim follows from `embedding_permutes_letters permEmb_holds D`.
-/
theorem embedding_permutes_letters_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.StandardLatticesGL3.EmbeddingPermutesTypes D := embedding_permutes_letters permEmb_holds D

/- English proof (translation)
The claim follows from `PI.character_extension_exists`.
-/
theorem charExt_holds : CharExt := PI.character_extension_exists

/- English proof (translation)
The claim follows from `sumEqTrace_holds`.
-/
theorem traceSum_holds : TraceSum := sumEqTrace_holds

/- English proof (translation)
The claim follows from `trace_sum_over_letters traceSum_holds D`.
-/
theorem trace_sum_over_letters_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.StandardLatticesGL3.TraceMapNormalisation D := trace_sum_over_letters traceSum_holds D

/- English proof (translation)
Assemble the required witnesses or components as `⟨Formalism.MainNotions.GL3Theta.induced_cm_type D, trace_sum_over_letters_holds D⟩`.
-/
theorem induced_type_from_K_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.StandardLatticesGL3.admG1 D := ⟨Formalism.MainNotions.GL3Theta.induced_cm_type D, trace_sum_over_letters_holds D⟩

end Formalism.MainNotions.Ext
