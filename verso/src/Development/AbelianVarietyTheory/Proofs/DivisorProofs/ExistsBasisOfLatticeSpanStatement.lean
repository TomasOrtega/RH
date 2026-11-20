import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisOfLatticeSpan
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsBasisOfLatticeSpan.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_basis_of_lattice_span : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (h N : ℕ) (g : Fin h → V), v.Integers O → Submodule.span C (Set.range g) = ⊤ → Module.finrank C V = N → ∃ b : Module.Basis (Fin N) C V, Submodule.span O (Set.range g) = Submodule.span O (Set.range b) := by
  first | exact @GlobalTheory.exists_basis_span_eq_span_of_valuation | exact GlobalTheory.exists_basis_span_eq_span_of_valuation | (intros; apply GlobalTheory.exists_basis_span_eq_span_of_valuation <;> assumption)
