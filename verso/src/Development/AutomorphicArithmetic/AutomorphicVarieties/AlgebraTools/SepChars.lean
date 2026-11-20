import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

/- English proof (translation)
Introduce `R Γ _ _ _ n ψ hcard hinj`. Set `χ : Fin n → Γ →* ResidueField R` to `fun i => (residue R : R →* ResidueField R).comp (ψ i)`. Establish `hχ : ∀ i g, χ i g = residue R (ψ i g)` using `fun i g => rfl`. Take `⟨a⟩` from `(Cardinal.le_def (Fin n) (ResidueField R)).mp (by rwa [Cardinal.mk_fin])`. Set `L : (Γ →₀ ResidueField R) →ₗ[ResidueField R] (Fin n → ResidueField R)` to `Finsupp.linearCombination (ResidueField R) (fun g i => χ i g)`.

Establish `hsurj : Function.Surjective L`. Rewrite using `[← LinearMap.range_eq_top]`. Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hle⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)`. Establish `hli` using `(linearIndependent_monoidHom Γ (ResidueField R)).comp χ hinj`.

Rewrite `hli` using `[Fintype.linearIndependent_iff]`. Set `c : Fin n → ResidueField R` to `fun i => f (fun j => if i = j then 1 else 0)`. Establish `hf : ∀ v, f v = ∑ i, v i * c i`. Introduce `v`. Use `conv_lhs => rw [pi_eq_sum_univ v]`.

Simplify using `[c, map_sum, map_smul]`. Establish `hc : ∀ i, c i = 0`. Apply `hli c` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Establish `hg : (fun i => χ i g) ∈ LinearMap.range L` using `⟨Finsupp.single g 1, by simp [L]⟩`.

Establish `h0` using `hle hg`. Rewrite `h0` using `[LinearMap.mem_ker, hf]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]`. Rewrite using `[← h0]`. Conclude with `Finset.sum_congr rfl (fun i _ => mul_comm _ _)`.

Apply `hf0` to reduce the goal to its premises. Use extensionality with `v`. Simplify using `[hf, hc]`. Take `⟨w, hw⟩` from `hsurj (fun i => a i)`. Set `s` to `Function.surjInv (IsLocalRing.residue_surjective (R := R))`.

Set `z : MonoidAlgebra R Γ` to `∑ g ∈ w.support, MonoidAlgebra.single g (s (w g))`. Establish `hz : ∀ i, residue R (MonoidAlgebra.lift R R Γ (ψ i) z) = a i`. Introduce `i`. Establish `hwi` using `congrFun hw i`. Rewrite using `[← hwi]`.

Simplify using `only [z, L, map_sum, MonoidAlgebra.lift_single, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, smul_eq_mul, map_mul, hχ]`. Use `Finset.sum_congr rfl (fun g _ => ?_)` and prove the remaining obligations. Rewrite using `[Function.surjInv_eq (IsLocalRing.residue_surjective (R := R))]`. Both sides reduce to the same expression. Use `⟨z, fun i j hij => ?_⟩` and prove the remaining obligations.

Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, hz, hz, sub_ne_zero]`. Conclude with `fun h => hij (a.injective h)`.
-/
theorem UpperTheory.V.AlgebraTools.sep_chars :
    ∀ {R Γ : Type} [CommRing R] [IsLocalRing R] [Monoid Γ] {n : ℕ} (ψ : Fin n → Γ →* R), (n : Cardinal) ≤ Cardinal.mk (ResidueField R) → Function.Injective (fun i => (residue R : R →* ResidueField R).comp (ψ i)) → ∃ z : MonoidAlgebra R Γ, ∀ i j, i ≠ j → IsUnit (MonoidAlgebra.lift R R Γ (ψ i) z - MonoidAlgebra.lift R R Γ (ψ j) z) := by
  intro R Γ _ _ _ n ψ hcard hinj
  let χ : Fin n → Γ →* ResidueField R := fun i => (residue R : R →* ResidueField R).comp (ψ i)
  have hχ : ∀ i g, χ i g = residue R (ψ i g) := fun i g => rfl
  obtain ⟨a⟩ := (Cardinal.le_def (Fin n) (ResidueField R)).mp (by rwa [Cardinal.mk_fin])
  let L : (Γ →₀ ResidueField R) →ₗ[ResidueField R] (Fin n → ResidueField R) :=
    Finsupp.linearCombination (ResidueField R) (fun g i => χ i g)
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hli := (linearIndependent_monoidHom Γ (ResidueField R)).comp χ hinj
    rw [Fintype.linearIndependent_iff] at hli
    let c : Fin n → ResidueField R := fun i => f (fun j => if i = j then 1 else 0)
    have hf : ∀ v, f v = ∑ i, v i * c i := by
      intro v
      conv_lhs => rw [pi_eq_sum_univ v]
      simp [c, map_sum, map_smul]
    have hc : ∀ i, c i = 0 := by
      apply hli c
      funext g
      have hg : (fun i => χ i g) ∈ LinearMap.range L :=
        ⟨Finsupp.single g 1, by simp [L]⟩
      have h0 := hle hg
      rw [LinearMap.mem_ker, hf] at h0
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h0]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    apply hf0
    ext v
    simp [hf, hc]
  obtain ⟨w, hw⟩ := hsurj (fun i => a i)
  let s := Function.surjInv (IsLocalRing.residue_surjective (R := R))
  let z : MonoidAlgebra R Γ := ∑ g ∈ w.support, MonoidAlgebra.single g (s (w g))
  have hz : ∀ i, residue R (MonoidAlgebra.lift R R Γ (ψ i) z) = a i := by
    intro i
    have hwi := congrFun hw i
    rw [← hwi]
    simp only [z, L, map_sum, MonoidAlgebra.lift_single, Finsupp.linearCombination_apply,
      Finsupp.sum, Finset.sum_apply, smul_eq_mul, map_mul, hχ]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Function.surjInv_eq (IsLocalRing.residue_surjective (R := R))]
    rfl
  refine ⟨z, fun i j hij => ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, hz, hz, sub_ne_zero]
  exact fun h => hij (a.injective h)
