import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleSubrepWithGroupAlgebraFixed

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FixedVec.exists_irreducible_subrep_fixed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsIrreducibleSubrepWithGroupAlgebraFixed.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.exists_irreducible_subrep_with_groupAlgebra_fixed : ∀ (G G' W : Type) [Group G] [Finite G] [Fintype G'] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (i : G' → G) (c : G' → ℂ) (x : W), x ≠ 0 → ∑ g, c g • ρ (i g) x = x → ∃ U : Subrepresentation ρ, FiniteDimensional ℂ U.toSubmodule ∧ U.toRepresentation.IsIrreducible ∧ ∃ y : U.toSubmodule, y ≠ 0 ∧ ∑ g, c g • U.toRepresentation (i g) y = y := by
  first | exact @GlobalTheory.FixedVec.exists_irreducible_subrep_fixed | exact GlobalTheory.FixedVec.exists_irreducible_subrep_fixed | (intros; apply GlobalTheory.FixedVec.exists_irreducible_subrep_fixed <;> assumption)
