import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricFixedMemClosureFiniteAlgZp
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.K5.GeoFix.fixed_mem_closure` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGeometricFixedMemClosureFiniteAlgZp.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.geometric_fixed_mem_closure_finite_algZp : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ x : Ω, (∀ g ∈ Ggeo p Ω, g x = x) → ∃ S : Finset Ω, (∀ s ∈ S, IsAlgZp p s) ∧
    x ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)) := by
  first | exact @GlobalTheory.K5.GeoFix.fixed_mem_closure | exact GlobalTheory.K5.GeoFix.fixed_mem_closure | (intros; apply GlobalTheory.K5.GeoFix.fixed_mem_closure <;> assumption)
