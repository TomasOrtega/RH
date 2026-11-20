import Mathlib

namespace GlobalTheory.CompanionTheory.EigenLift

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Use `haveI : FiniteDimensional ℂ W' := Module.Finite.of_surjective (R := ℂ) f hf`. Use `set A : W →ₗ[ℂ] W := T - c • LinearMap.id with hA`. Use `set B : W' →ₗ[ℂ] W' := S - c • LinearMap.id with hB`.

Establish `hinj : Function.Injective A`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `w hw`. Assume the negation of the conclusion as `h0`. Apply `hne w h0` to reduce the goal to its premises.

Simplify `hw` using `[hA, sub_eq_zero]`. Establish `hsurjT : Function.Surjective A` using `LinearMap.injective_iff_surjective.1 hinj`. Establish `hcomm : ∀ z, f (A z) = B (f z)`. Introduce `z`. Establish `h1` using `LinearMap.congr_fun hfT z`.

Simplify using `only [LinearMap.comp_apply] at h1`. Simplify using `[hA, hB, map_sub, map_smul, h1]`. Establish `hsurjS : Function.Surjective B`. Introduce `y`. Take `⟨x, rfl⟩` from `hf y`.

Take `⟨z, rfl⟩` from `hsurjT x`. Conclude with `⟨f z, (hcomm z).symm⟩`. Establish `hinjS` using `LinearMap.injective_iff_surjective.2 hsurjS`. Apply `hw'` to reduce the goal to its premises. Apply `hinjS` to reduce the goal to its premises.

Simplify using `[hB, hS]`.
-/
theorem exists_eigenvector_of_surjective_intertwiner
    (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W')
    (hf : Function.Surjective f) (hfT : f ∘ₗ T = S ∘ₗ f)
    (c : ℂ) (w' : W') (hw' : w' ≠ 0) (hS : S w' = c • w') :
    ∃ w : W, w ≠ 0 ∧ T w = c • w := by
  by_contra hne
  push_neg at hne
  haveI : FiniteDimensional ℂ W' := Module.Finite.of_surjective (R := ℂ) f hf
  set A : W →ₗ[ℂ] W := T - c • LinearMap.id with hA
  set B : W' →ₗ[ℂ] W' := S - c • LinearMap.id with hB
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra h0
    apply hne w h0
    simpa [hA, sub_eq_zero] using hw
  have hsurjT : Function.Surjective A := LinearMap.injective_iff_surjective.1 hinj
  have hcomm : ∀ z, f (A z) = B (f z) := by
    intro z
    have h1 := LinearMap.congr_fun hfT z
    simp only [LinearMap.comp_apply] at h1
    simp [hA, hB, map_sub, map_smul, h1]
  have hsurjS : Function.Surjective B := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    obtain ⟨z, rfl⟩ := hsurjT x
    exact ⟨f z, (hcomm z).symm⟩
  have hinjS := LinearMap.injective_iff_surjective.2 hsurjS
  apply hw'
  apply hinjS
  simp [hB, hS]

/- English proof (translation)
Introduce `W W' _ _ _ _ _ T S f hf hfT c w' hw' hS _`. Conclude with `exists_eigenvector_of_surjective_intertwiner W W' T S f hf hfT c w' hw' hS`.
-/
theorem nonzero_eigenvalue_lifts :
    ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
      [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W'),
      Function.Surjective f → f ∘ₗ T = S ∘ₗ f →
      ∀ (c : ℂ) (w' : W'), w' ≠ 0 → S w' = c • w' → c ≠ 0 → ∃ w : W, w ≠ 0 ∧ T w = c • w := by
  intro W W' _ _ _ _ _ T S f hf hfT c w' hw' hS _
  exact exists_eigenvector_of_surjective_intertwiner W W' T S f hf hfT c w' hw' hS

end GlobalTheory.CompanionTheory.EigenLift
