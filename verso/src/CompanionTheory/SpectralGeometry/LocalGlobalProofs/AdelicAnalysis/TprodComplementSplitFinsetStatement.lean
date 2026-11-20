import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TprodComplementSplitFinset
import Mathlib
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FTprodComplementSplitFinset.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.tprod_complement_split_finset : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (S S' : Finset ι), Summable (fun v => |a v - 1|) → S ⊆ S' → ∏' v : {v // v ∉ S}, a v.1 = (∏ v ∈ S' \ S, a v) * ∏' v : {v // v ∉ S'}, a v.1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut | exact GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut | (intros; apply GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut <;> assumption)
