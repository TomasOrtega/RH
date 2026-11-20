import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt

open UpperTheory.V.Z.Mult UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.V.Z.Mult.offSec :
    UpperTheory.V.Z.Mult.OffSec := by
  intro E _ _ _ n S K' K'' h
  unfold GlobalTheory.BCT.globLev
  refine iInf_congr fun w => iInf_congr fun hw => ?_
  rw [h w hw]
