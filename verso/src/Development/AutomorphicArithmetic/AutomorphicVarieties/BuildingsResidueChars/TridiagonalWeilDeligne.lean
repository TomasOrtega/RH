import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs

noncomputable section

open Module

namespace UpperTheory

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)` and prove the remaining obligations. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[hA i k h, zero_mul]`. Rewrite using `[hB k i h, mul_zero]`.
-/
private theorem tri_mul_diag {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hA i k h, zero_mul]
  · rw [hB k i h, mul_zero]

/- English proof (translation)
Use `letI := Fintype.ofFinite G`. Establish `hm : ∀ g h i, R (g * h) i i = R g i i * R h i i` using `fun g h i => by`. Rewrite using `[map_mul]`. Conclude with `tri_mul_diag _ _ (hR g) (hR h) i`. Use `⟨∑ h, R h * Matrix.diagonal (fun i => R h⁻¹ i i), ?_, fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_of_upperTriangular]`. Rewrite using `[isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]`. Introduce `i _`. Establish `: (∑ h, R h * Matrix.diagonal (fun i => R h⁻¹ i i)) i i = (Fintype.card G : ℂ)`. Rewrite using `[Matrix.sum_apply]`.

Establish `: ∀ h : G, (R h * Matrix.diagonal (fun i => R h⁻¹ i i)) i i = 1` using `fun h => by`. Rewrite using `[Matrix.mul_diagonal, ← hm, mul_inv_cancel, map_one, Matrix.one_apply_eq]`. Simplify using `[this]`. Rewrite using `[this]`. Conclude with `Fintype.card_ne_zero` after adjusting the coercions.

Introduce `i j hij`. Rewrite using `[Matrix.sum_apply]`. Use `Finset.sum_eq_zero fun h _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_diagonal, hR h i j hij, zero_mul]`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`.

Use `Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_` and prove the remaining obligations. Rewrite using `[Equiv.coe_mulLeft, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, map_mul, Matrix.mul_assoc]`. Use `congr 3`. Use function extensionality and compare the values at `i`. Rewrite using `[← hm]`.

Use `congr 2`. Use `group`.
-/
private theorem tri_avg {G : Type} [Group G] [Finite G] {n : ℕ} (R : G →* Matrix (Fin n) (Fin n) ℂ)
    (hR : ∀ g i j, j < i → R g i j = 0) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P.det ∧ ∀ g, R g * P = P * Matrix.diagonal (fun i => R g i i) := by
  classical
  letI := Fintype.ofFinite G
  have hm : ∀ g h i, R (g * h) i i = R g i i * R h i i := fun g h i => by
    rw [map_mul]; exact tri_mul_diag _ _ (hR g) (hR h) i
  refine ⟨∑ h, R h * Matrix.diagonal (fun i => R h⁻¹ i i), ?_, fun g => ?_⟩
  · rw [Matrix.det_of_upperTriangular]
    · rw [isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
      intro i _
      have : (∑ h, R h * Matrix.diagonal (fun i => R h⁻¹ i i)) i i = (Fintype.card G : ℂ) := by
        rw [Matrix.sum_apply]
        have : ∀ h : G, (R h * Matrix.diagonal (fun i => R h⁻¹ i i)) i i = 1 := fun h => by
          rw [Matrix.mul_diagonal, ← hm, mul_inv_cancel, map_one, Matrix.one_apply_eq]
        simp [this]
      rw [this]
      exact_mod_cast Fintype.card_ne_zero
    · intro i j hij
      rw [Matrix.sum_apply]
      refine Finset.sum_eq_zero fun h _ => ?_
      rw [Matrix.mul_diagonal, hR h i j hij, zero_mul]
  · rw [Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
    rw [Equiv.coe_mulLeft, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, map_mul, Matrix.mul_assoc]
    congr 3
    funext i
    rw [← hm]
    congr 2
    group

/- English proof (translation)
Introduce `W I _ _ _ n ρ d hfin ⟨b, hb⟩`. Set `G` to `ρ.toHomUnits.range`. Use `haveI : Finite G := by haveI : Finite (Set.range ρ) := hfin`. Use `Finite.of_injective (fun g : G => (⟨(g.1 : End ℂ W), ?_⟩ : Set.range ρ)) ?_` and prove the remaining obligations. Take `⟨s, hs⟩` from `g.2`.

Conclude with `⟨s, by rw [← hs]; rfl⟩`. Introduce `x y h`. Conclude with `Subtype.ext (Units.ext (congrArg Subtype.val h))`. Set `R : G →* Matrix (Fin n) (Fin n) ℂ` to `((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp (Units.coeHom _)).comp G.subtype`. Establish `hRs : ∀ s, R (ρ.toHomUnits.rangeRestrict s) = LinearMap.toMatrix b b (ρ s)` using `fun s => rfl`.

Take `⟨P, hP, hRP⟩` from `tri_avg R (fun g i j hij => by`. Take `⟨s, rfl⟩` from `ρ.toHomUnits.rangeRestrict_surjective g`. Rewrite using `[hRs]`. Conclude with `(hb s).1 i j hij)`. Set `e` to `Matrix.toLinearEquiv b P hP`.

Establish `he : ∀ x, e x = Matrix.toLin b b P x` using `fun x => rfl`. Use `⟨b.map e, fun s => ?_⟩` and prove the remaining obligations. Establish `h1` using `hRP (ρ.toHomUnits.rangeRestrict s)`. Rewrite `h1` using `[hRs]`. Establish `h2 : (fun i => LinearMap.toMatrix b b (ρ s) i i) = d s` using `funext (hb s).2`.

Rewrite `h1` using `[h2]`. Establish `h3 : ∀ j, ρ s (b.map e j) = d s j • b.map e j` using `fun j => by`. Establish `h4` using `congrArg (fun M => Matrix.toLin b b M (b j)) h1`. Simplify using `only [Matrix.toLin_mul b b b, Matrix.toLin_toMatrix, LinearMap.comp_apply] at h4`. Rewrite using `[Basis.map_apply, he, h4, ← map_smul]`.

Use `congr 1`. Rewrite using `[Matrix.toLin_self]`. Simplify using `[Matrix.diagonal_apply, ite_smul, Finset.sum_ite_eq']`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, h3, map_smul, Basis.repr_self, Matrix.diagonal_apply]`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Finsupp.single_apply, Ne.symm h]`.
-/
theorem tridiagonal_weil_deligne : UpperTheory.V.Af.Wd.TriDiag := by
  intro W I _ _ _ n ρ d hfin ⟨b, hb⟩
  let G := ρ.toHomUnits.range
  haveI : Finite G := by
    haveI : Finite (Set.range ρ) := hfin
    refine Finite.of_injective (fun g : G => (⟨(g.1 : End ℂ W), ?_⟩ : Set.range ρ)) ?_
    · obtain ⟨s, hs⟩ := g.2
      exact ⟨s, by rw [← hs]; rfl⟩
    · intro x y h
      exact Subtype.ext (Units.ext (congrArg Subtype.val h))
  let R : G →* Matrix (Fin n) (Fin n) ℂ :=
    ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp (Units.coeHom _)).comp G.subtype
  have hRs : ∀ s, R (ρ.toHomUnits.rangeRestrict s) = LinearMap.toMatrix b b (ρ s) := fun s => rfl
  obtain ⟨P, hP, hRP⟩ := tri_avg R (fun g i j hij => by
    obtain ⟨s, rfl⟩ := ρ.toHomUnits.rangeRestrict_surjective g
    rw [hRs]; exact (hb s).1 i j hij)
  let e := Matrix.toLinearEquiv b P hP
  have he : ∀ x, e x = Matrix.toLin b b P x := fun x => rfl
  refine ⟨b.map e, fun s => ?_⟩
  have h1 := hRP (ρ.toHomUnits.rangeRestrict s)
  rw [hRs] at h1
  have h2 : (fun i => LinearMap.toMatrix b b (ρ s) i i) = d s := funext (hb s).2
  rw [h2] at h1
  have h3 : ∀ j, ρ s (b.map e j) = d s j • b.map e j := fun j => by
    have h4 := congrArg (fun M => Matrix.toLin b b M (b j)) h1
    simp only [Matrix.toLin_mul b b b, Matrix.toLin_toMatrix, LinearMap.comp_apply] at h4
    rw [Basis.map_apply, he, h4, ← map_smul]
    congr 1
    rw [Matrix.toLin_self]
    simp [Matrix.diagonal_apply, ite_smul, Finset.sum_ite_eq']
  ext i j
  rw [LinearMap.toMatrix_apply, h3, map_smul, Basis.repr_self, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Finsupp.single_apply, Ne.symm h]

end UpperTheory
