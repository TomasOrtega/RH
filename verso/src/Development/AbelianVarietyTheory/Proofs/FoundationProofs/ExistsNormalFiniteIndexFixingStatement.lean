import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalFiniteIndexFixing
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AlmostEt.exists_normal_finiteIndex_fixing` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsNormalFiniteIndexFixing.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_normal_finiteIndex_fixing_finite_orbits : ∀ (L : Type) [Field L] (G : Type) [Group G] [MulSemiringAction G L] (S : Finset L), (∀ s ∈ S, (MulAction.orbit G s).Finite) → ∃ U : Subgroup G, U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix L U) ∧ ∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x := by
  first | exact @GlobalTheory.AlmostEt.exists_normal_finiteIndex_fixing | exact GlobalTheory.AlmostEt.exists_normal_finiteIndex_fixing | (intros; apply GlobalTheory.AlmostEt.exists_normal_finiteIndex_fixing <;> assumption)
