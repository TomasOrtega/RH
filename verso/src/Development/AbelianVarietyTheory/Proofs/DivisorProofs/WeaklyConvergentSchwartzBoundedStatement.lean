import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeaklyConvergentSchwartzBounded
import Mathlib
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeaklyConvergentSchwartzBounded.lean&line=114#L114)
-/
theorem _root_.GlobalTheory.T.weakly_convergent_schwartz_bounded : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : ℕ → SchwartzMap V ℂ) (f₀ : SchwartzMap V ℂ), (∀ T : SchwartzMap V ℂ →L[ℂ] ℂ, Tendsto (fun j => T (f j)) atTop (𝓝 (T f₀))) → ∀ k n : ℕ, BddAbove (Set.range fun j => SchwartzMap.seminorm ℂ k n (f j)) := by
  first | exact @GlobalTheory.SchwartzMap.bddAbove_seminorm_of_weak_tendsto | exact GlobalTheory.SchwartzMap.bddAbove_seminorm_of_weak_tendsto | (intros; apply GlobalTheory.SchwartzMap.bddAbove_seminorm_of_weak_tendsto <;> assumption)
