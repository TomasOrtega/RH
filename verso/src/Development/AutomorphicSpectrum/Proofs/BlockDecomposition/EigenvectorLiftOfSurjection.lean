import Mathlib

namespace GlobalTheory.CompanionTheory.EigenLift

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction.

Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem nonzero_eigenvalue_lifts :
    ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
      [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (S : W' →ₗ[ℂ] W') (f : W →ₗ[ℂ] W'),
      Function.Surjective f → f ∘ₗ T = S ∘ₗ f →
      ∀ (c : ℂ) (w' : W'), w' ≠ 0 → S w' = c • w' → c ≠ 0 → ∃ w : W, w ≠ 0 ∧ T w = c • w := by
  intro W W' _ _ _ _ _ T S f hf hfT c w' hw' hS _
  exact exists_eigenvector_of_surjective_intertwiner W W' T S f hf hfT c w' hw' hS

end GlobalTheory.CompanionTheory.EigenLift
