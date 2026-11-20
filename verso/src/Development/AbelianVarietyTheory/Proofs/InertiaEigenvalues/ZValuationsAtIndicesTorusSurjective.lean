import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValsAtApply
open GlobalTheory.UnitLemma

namespace GlobalTheory.UnitLemma

/- English proof (translation)
Introduce `G _ τ hττ T hT ι s w hsw hex r e he hs n`. Use `choose y hy1 hy2 using fun j : Fin r => hex (e j) (Multiplicative.toAdd n j)`. Establish `hτ : ∀ i j, w (e i) (τ (y j)) = 1`. Introduce `i j`. Establish `h1 : w (s (e i)) (y j) = 1` using `hy2 j _ (hs i j)`.

Establish `a` using `(hsw (e i) (y j)).1 (by rw [h1]; simp)`. Establish `b` using `(hsw (e i) (y j)⁻¹).1 (by rw [map_inv, h1]; simp)`. Rewrite `b` using `[map_inv, map_inv, toAdd_inv]`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Simplify using `only [toAdd_one]`.

Use linear arithmetic over natural numbers and integers. Establish `hu : ∀ j, y j * (τ (y j))⁻¹ ∈ T`. Introduce `j`. Rewrite using `[hT, map_mul, map_inv, hττ]`. Use `group`.

Use `⟨⟨∏ j, y j * (τ (y j))⁻¹, Subgroup.prod_mem T fun j _ => hu j⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [MonoidHom.comp_apply, Subgroup.coe_subtype]`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Rewrite using `[valsAt_apply, map_prod, toAdd_prod]`.

Establish `hc : ∀ j, Multiplicative.toAdd (w (e i) (y j * (τ (y j))⁻¹)) = if i = j then Multiplicative.toAdd n i else 0`. Introduce `j`. Rewrite using `[map_mul, map_inv, hτ, inv_one, mul_one]`. Use `split_ifs with hij`. Substitute `hij` using the available equality.

Rewrite using `[hy1]`. Both sides reduce to the same expression. Rewrite using `[hy2 j (e i) fun h => hij (he _ _ h)]`. Both sides reduce to the same expression. Simplify using `only [hc, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
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
