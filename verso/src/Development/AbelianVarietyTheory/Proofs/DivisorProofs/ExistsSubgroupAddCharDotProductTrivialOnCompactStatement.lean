import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubgroupAddCharDotProductTrivialOnCompact
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CharDotKill.charDot_kill` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSubgroupAddCharDotProductTrivialOnCompact.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.exists_subgroup_addChar_dotProduct_trivial_on_compact : ∀ {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [NonarchimedeanAddGroup K] (χ : AddChar K ℂ), Continuous χ → ∀ (κ : Type) [Fintype κ] (C : Set (κ → K)), IsCompact C → ∃ H : OpenAddSubgroup (κ → K), ∀ z ∈ C, ∀ a ∈ H, ∀ b ∈ H, χ (z ⬝ᵥ b + a ⬝ᵥ b) = 1 := by
  first | exact @GlobalTheory.CharDotKill.charDot_kill | exact GlobalTheory.CharDotKill.charDot_kill | (intros; apply GlobalTheory.CharDotKill.charDot_kill <;> assumption)
