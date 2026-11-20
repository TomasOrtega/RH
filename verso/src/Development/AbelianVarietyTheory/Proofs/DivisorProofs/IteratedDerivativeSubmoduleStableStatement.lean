import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeSubmoduleStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIteratedDerivativeSubmoduleStable.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.kernel_rationality_of_reciprocity : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → KerRatAt := by
  first | exact @GlobalTheory.BigOn.Exp.SerBase.kerRatAt | exact GlobalTheory.BigOn.Exp.SerBase.kerRatAt | (intros; apply GlobalTheory.BigOn.Exp.SerBase.kerRatAt <;> assumption)
