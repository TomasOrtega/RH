import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValsAtApply
open GlobalTheory.UnitLemma

namespace GlobalTheory.UnitLemma

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem valsAt_torus_surjective : ∀ (G : Type) [CommGroup G] (τ : G →* G), (∀ x, τ (τ x) = x) → ∀ (T : Subgroup G), (∀ t, t ∈ T ↔ t * τ t = 1) → ∀ (ι : Type) (s : ι → ι) (w : ι → G →* Multiplicative ℤ), (∀ i x, 0 ≤ Multiplicative.toAdd (w (s i) x) ↔ 0 ≤ Multiplicative.toAdd (w i (τ x))) → (∀ i (n : ℤ), ∃ y : G, w i y = Multiplicative.ofAdd n ∧ ∀ j, j ≠ i → w j y = 1) → ∀ (r : ℕ) (e : Fin r → ι), (∀ j k, e j = e k → j = k) → (∀ j k, s (e j) ≠ e k) → Function.Surjective ((valsAt w e).comp T.subtype) := by
  intro G _ τ hττ T hT ι s w hsw hex r e he hs n
  choose y hy1 hy2 using fun j : Fin r => hex (e j) (Multiplicative.toAdd n j)
  have hτ : ∀ i j, w (e i) (τ (y j)) = 1 := by
    intro i j
    have h1 : w (s (e i)) (y j) = 1 := hy2 j _ (hs i j)
    have a := (hsw (e i) (y j)).1 (by rw [h1]; simp)
    have b := (hsw (e i) (y j)⁻¹).1 (by rw [map_inv, h1]; simp)
    rw [map_inv, map_inv, toAdd_inv] at b
    apply Multiplicative.toAdd.injective
    simp only [toAdd_one]
    omega
  have hu : ∀ j, y j * (τ (y j))⁻¹ ∈ T := by
    intro j
    rw [hT, map_mul, map_inv, hττ]
    group
  refine ⟨⟨∏ j, y j * (τ (y j))⁻¹, Subgroup.prod_mem T fun j _ => hu j⟩, ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  apply Multiplicative.toAdd.injective
  funext i
  rw [valsAt_apply, map_prod, toAdd_prod]
  have hc : ∀ j, Multiplicative.toAdd (w (e i) (y j * (τ (y j))⁻¹)) = if i = j then Multiplicative.toAdd n i else 0 := by
    intro j
    rw [map_mul, map_inv, hτ, inv_one, mul_one]
    split_ifs with hij
    · subst hij; rw [hy1]; rfl
    · rw [hy2 j (e i) fun h => hij (he _ _ h)]; rfl
  simp only [hc, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory.UnitLemma
