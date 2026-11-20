import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZValuationsAtIndicesTorusSurjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValsAtApply
open GlobalTheory.UnitLemma
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.valsAt_torus_surjective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FZValuationsAtIndicesTorusSurjective.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.zValuationsAtIndices_torus_surjective : ∀ (G : Type) [CommGroup G] (τ : G →* G), (∀ x, τ (τ x) = x) → ∀ (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → (∀ i (n : ℤ), ∃ y : G, w i y = Multiplicative.ofAdd n ∧ ∀ j, j ≠ i → w j y = 1) → ∀ (r : ℕ) (e : Fin r → ι), (∀ j k, e j = e k → j = k) → (∀ j k, s (e j) ≠ e k) → Function.Surjective ((valsAt w e).comp T.subtype) := by
  first | exact @GlobalTheory.UnitLemma.valsAt_torus_surjective | exact GlobalTheory.UnitLemma.valsAt_torus_surjective | (intros; apply GlobalTheory.UnitLemma.valsAt_torus_surjective <;> assumption)
