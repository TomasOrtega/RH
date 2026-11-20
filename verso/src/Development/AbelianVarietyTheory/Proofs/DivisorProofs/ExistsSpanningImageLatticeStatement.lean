import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningImageLattice
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.image_integral_points_eq_span_of_surjective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSpanningImageLattice.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_spanning_image_lattice : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (h : ℕ) (π : (Fin h → C) →ₗ[C] V), Function.Surjective π → ∃ g : Fin h → V, Submodule.span C (Set.range g) = ⊤ ∧ Set.range (fun t : Fin h → O => π (fun i => algebraMap O C (t i))) = (Submodule.span O (Set.range g) : Set V) := by
  first | exact @GlobalTheory.image_integral_points_eq_span_of_surjective | exact GlobalTheory.image_integral_points_eq_span_of_surjective | (intros; apply GlobalTheory.image_integral_points_eq_span_of_surjective <;> assumption)
