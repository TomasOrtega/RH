import Mathlib
open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Introduce `Z R _ _ _ σ hσ lam hlam hbij N ψ halt hψ hadj`. Establish `hskew : ∀ x y, ψ x y = -ψ y x` using `fun x y => by`. Use `halt (x + y)` as an intermediate fact. Simplify using `only [map_add, LinearMap.add_apply, halt] at this`. Take the linear combination `this`.

Establish `hinj : ∀ a b : R, (∀ r, lam (a * r) = lam (b * r)) → a = b` using `fun a b h => hbij.1 (LinearMap.ext fun r => h r)`. Establish `hex : ∀ i j : Fin N, ∃ a : R, ∀ r : R, lam (a * r) = ψ (r • Pi.single i 1) (Pi.single j 1)`. Introduce `i j`. Take `⟨a, ha⟩` from `hbij.2 ((ψ.flip (Pi.single j 1)).comp ((LinearMap.toSpanSingleton R (Fin N → R) (Pi.single i 1)).restrictScalars Z))`. Conclude with `⟨a, fun r => LinearMap.congr_fun ha r⟩`.

Use `choose A hA using hex`. Establish `hform : ∀ x y, ψ x y = lam (∑ i, ∑ j, x i * A i j * σ (y j))`. Introduce `x y`. Use `conv_lhs => rw [pi_eq_sum_univ' x, pi_eq_sum_univ' y]`. Simplify using `only [map_sum, LinearMap.sum_apply]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h1` using `hadj (σ (y j)) (x i • Pi.single i 1) (Pi.single j 1)`. Rewrite `h1` using `[hσ, smul_smul, ← hA]`. Rewrite using `[← h1]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `⟨Matrix.of A, ?_, ?_, hform⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]`.

Use `hinj _ _ fun r => ?_` and prove the remaining obligations. Establish `h1` using `hlam (A j i * σ r)`. Rewrite `h1` using `[map_mul, hσ]`. Rewrite using `[h1, hA, hA, hadj r, hskew (Pi.single i 1)]`. Rewrite using `[← Matrix.isUnit_iff_isUnit_det, ← Matrix.vecMul_surjective_iff_isUnit]`.

Introduce `w`. Set `F : (Fin N → R) →ₗ[Z] Z` to `∑ j, lam.comp ((LinearMap.mulLeft Z (w j)).comp (σ.toLinearMap.comp ((LinearMap.proj j : (Fin N → R) →ₗ[R] R).restrictScalars Z)))`. Take `⟨x, hx⟩` from `hψ.2 F`. Use `⟨x, funext fun j => hinj _ _ fun r => ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun hx (Pi.single j (σ r))`.

Rewrite `h1` using `[hform]`. Simplify using `only [F, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply] at h1`. Establish `h2 : ∑ d, lam (w d * σ (Pi.single (M` using `fun _ => R) j (σ r) d)) = lam (w j * r) := by`. Rewrite using `[Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp), Pi.single_eq_same, hσ]`. Rewrite using `[← h2, ← h1]`.

Use `congr 1`. Simplify using `only [Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp), Pi.single_eq_same, hσ]`.
-/
theorem tw_g_herm : ∀ (Z R : Type) [CommRing Z] [CommRing R] [Algebra Z R] (σ : R →ₐ[Z] R), (∀ r, σ (σ r) = r) → ∀ lam : R →ₗ[Z] Z, (∀ r, lam (σ r) = -lam r) → Function.Bijective (fun r : R => lam.comp (LinearMap.mulLeft Z r)) → ∀ (N : ℕ) (ψ : LinearMap.BilinForm Z (Fin N → R)), (∀ x, ψ x x = 0) → Function.Bijective ψ → (∀ (a : R) x y, ψ (a • x) y = ψ x (σ a • y)) → ∃ A : Matrix (Fin N) (Fin N) R, (A.map σ).transpose = A ∧ IsUnit A.det ∧ ∀ x y, ψ x y = lam (∑ i, ∑ j, x i * A i j * σ (y j)) := by
  intro Z R _ _ _ σ hσ lam hlam hbij N ψ halt hψ hadj
  have hskew : ∀ x y, ψ x y = -ψ y x := fun x y => by
    have := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt] at this
    linear_combination this
  have hinj : ∀ a b : R, (∀ r, lam (a * r) = lam (b * r)) → a = b := fun a b h =>
    hbij.1 (LinearMap.ext fun r => h r)
  have hex : ∀ i j : Fin N, ∃ a : R, ∀ r : R, lam (a * r) = ψ (r • Pi.single i 1) (Pi.single j 1) := by
    intro i j
    obtain ⟨a, ha⟩ := hbij.2 ((ψ.flip (Pi.single j 1)).comp
      ((LinearMap.toSpanSingleton R (Fin N → R) (Pi.single i 1)).restrictScalars Z))
    exact ⟨a, fun r => LinearMap.congr_fun ha r⟩
  choose A hA using hex
  have hform : ∀ x y, ψ x y = lam (∑ i, ∑ j, x i * A i j * σ (y j)) := by
    intro x y
    conv_lhs => rw [pi_eq_sum_univ' x, pi_eq_sum_univ' y]
    simp only [map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h1 := hadj (σ (y j)) (x i • Pi.single i 1) (Pi.single j 1)
    rw [hσ, smul_smul, ← hA] at h1
    rw [← h1]
    congr 1; ring
  refine ⟨Matrix.of A, ?_, ?_, hform⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
    refine hinj _ _ fun r => ?_
    have h1 := hlam (A j i * σ r)
    rw [map_mul, hσ] at h1
    rw [h1, hA, hA, hadj r, hskew (Pi.single i 1)]
  · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.vecMul_surjective_iff_isUnit]
    intro w
    let F : (Fin N → R) →ₗ[Z] Z := ∑ j, lam.comp ((LinearMap.mulLeft Z (w j)).comp
      (σ.toLinearMap.comp ((LinearMap.proj j : (Fin N → R) →ₗ[R] R).restrictScalars Z)))
    obtain ⟨x, hx⟩ := hψ.2 F
    refine ⟨x, funext fun j => hinj _ _ fun r => ?_⟩
    have h1 := LinearMap.congr_fun hx (Pi.single j (σ r))
    rw [hform] at h1
    simp only [F, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.proj_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply] at h1
    have h2 : ∑ d, lam (w d * σ (Pi.single (M := fun _ => R) j (σ r) d)) = lam (w j * r) := by
      rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp),
        Pi.single_eq_same, hσ]
    rw [← h2, ← h1]
    congr 1
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp),
      Pi.single_eq_same, hσ]

end PositivityTheory.UnitarySelfGeneration
