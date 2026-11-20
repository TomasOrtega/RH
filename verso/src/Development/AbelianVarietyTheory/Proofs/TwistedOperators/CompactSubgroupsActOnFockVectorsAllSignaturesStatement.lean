import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FCompactSubgroupsActOnFockVectorsAllSignatures.lean&line=460#L460)
-/
theorem _root_.GlobalTheory.T.compact_subgroups_act_on_fock_vectors_all_signatures : ∀ D : D7, GlobalTheory.ChainFr.CompactFockAll D := by
  first | exact @GlobalTheory.CompactFockAction.compactFockAll | exact GlobalTheory.CompactFockAction.compactFockAll | (intros; apply GlobalTheory.CompactFockAction.compactFockAll <;> assumption)
