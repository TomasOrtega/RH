import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open GlobalTheory.BCT

/- English proof (translation)
Introduce `G _ K u hu`. Establish `hK : rStab u ⊓ K = K` using `inf_eq_right.mpr fun k hk x => hu k hk x`. Unfold `hint`. Rewrite using `[hK, Subgroup.relIndex_self]`. Simplify using the standard rewrite rules.
-/
theorem hintSph : HintSph := by
  intro G _ K u hu
  have hK : rStab u ⊓ K = K := inf_eq_right.mpr fun k hk x => hu k hk x
  unfold hint
  rw [hK, Subgroup.relIndex_self]
  simp

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
