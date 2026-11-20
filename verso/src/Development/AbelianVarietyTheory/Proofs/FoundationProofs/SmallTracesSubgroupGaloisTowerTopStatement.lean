import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmallTracesSubgroupGaloisTowerTop
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSmallTracesSubgroupGaloisTowerTop.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.smallTraces_subgroup_galois_towerTop : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (H : Subgroup (Gal p Ω)), H ≤ ⨅ n, Gn T n → ∀ (S : Finset Ω) (j : ℕ), 1 ≤ j → ∃ (y : Ω) (E : Finset (Gal p Ω)), IsInt p y ∧ (∀ g ∈ E, g ∈ H) ∧ (∀ h ∈ H, ∃! g, g ∈ E ∧ h y = g y ∧ ∀ s ∈ S, h s = g s) ∧ ∑ g ∈ E, g y = T.ζ j - 1 := by
  first | exact @GlobalTheory.K5.small_traces_subgroup | exact GlobalTheory.K5.small_traces_subgroup | (intros; apply GlobalTheory.K5.small_traces_subgroup <;> assumption)
