import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneLatticeSpanSingleton
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finGen_line_span_principal_target` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRankOneLatticeSpanSingleton.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.rank_one_lattice_span_singleton : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (I : Type) [Finite I] (u : I → V), v.Integers O → Module.finrank C V = 1 → (∃ i, u i ≠ 0) → ∃ w : V, w ≠ 0 ∧ Submodule.span O (Set.range u) = Submodule.span O {w} := by
  first | exact @GlobalTheory.finGen_line_span_principal_target | exact GlobalTheory.finGen_line_span_principal_target | (intros; apply GlobalTheory.finGen_line_span_principal_target <;> assumption)
