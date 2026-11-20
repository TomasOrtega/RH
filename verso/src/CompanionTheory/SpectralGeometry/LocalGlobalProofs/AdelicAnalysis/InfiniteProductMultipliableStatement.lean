import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FInfiniteProductMultipliable.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.infinite_product_multipliable : ∀ (ι : Type) (a : ι → ℝ), Summable (fun v => |a v - 1|) → Multipliable a ∧ (∀ S : Finset ι, Multipliable (fun v : {v // v ∉ S} => a v.1) ∧ ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1) ∧ ((∀ v, 0 < a v) → 0 < ∏' v, a v) ∧ ((∀ v, 0 ≤ a v) → 0 ≤ ∏' v, a v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod | exact GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod | (intros; apply GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod <;> assumption)
