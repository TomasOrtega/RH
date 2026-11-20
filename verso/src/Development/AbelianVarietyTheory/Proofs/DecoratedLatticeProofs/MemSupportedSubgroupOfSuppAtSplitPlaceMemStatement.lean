import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FMemSupportedSubgroupOfSuppAtSplitPlaceMem.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.mem_supportedSubgroup_of_suppAt_splitPlace_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V), SuppAt q.e V g → ∀ P : GlobalTheory.FinPl.Pl D → Prop, P q.v → g ∈ GlobalTheory.FinPl.grpAt V P := by
  first | exact @GlobalTheory.SuppGrp.mem_grpAt_of_suppAt | exact GlobalTheory.SuppGrp.mem_grpAt_of_suppAt | (intros; apply GlobalTheory.SuppGrp.mem_grpAt_of_suppAt <;> assumption)
