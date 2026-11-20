import Mathlib
open scoped Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `O _ _ c hc h2 n J hJ hdet Z₀ hZ`. Take `⟨u, hu⟩ : ∃ u : O, u * 2 = 1` from `⟨h2.unit⁻¹.val, h2.val_inv_mul⟩`. Establish `hcu : c u = u`. Establish `h1 : c u * 2 = 1`. Use `congrArg c hu` as an intermediate fact.

Simplify `this` using `[map_mul, map_ofNat]`. Combine the equalities or inequalities in the displayed calculation. Use `set E := Z₀ᵀ * J + J * Z₀.map c with hE`. Establish `hJc : (J.map c)ᵀ = J`. Use extensionality with `i j`.

Simplify using `[Matrix.transpose_apply, Matrix.map_apply, hJ]`. Establish `hEc : (E.map c)ᵀ = E`. Use extensionality with `i j`. Simplify using `only [hE, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add, map_sum, map_mul, hc, hJ]`. Rewrite using `[add_comm]`.

Apply the tactic sequence `congr 1 <;> refine Finset.sum_congr rfl (fun k _ => ?_) <;> ring`. Establish `hJinv : J * ((J⁻¹).map c)ᵀ = 1`. Combine the equalities or inequalities in the displayed calculation. Use `set D := (u • (E * J⁻¹))ᵀ with hD`. Establish `hDT : Dᵀ * J = u • E`.

Rewrite using `[hD, Matrix.transpose_transpose, Matrix.smul_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul J hdet, Matrix.mul_one]`. Establish `hDmap : D.map c = u • (((J⁻¹).map c)ᵀ * (E.map c)ᵀ)`. Rewrite using `[← Matrix.transpose_mul, ← Matrix.map_mul, hD]`. Use extensionality with `i j`. Simplify using `[Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, map_sum, map_mul, hcu]`.

Establish `hDc : J * D.map c = u • E`. Rewrite using `[hDmap, Matrix.mul_smul, ← Matrix.mul_assoc, hJinv, Matrix.one_mul, hEc]`. Use `⟨Z₀ - D, ?_, ?_⟩` and prove the remaining obligations. Establish `hmap : (Z₀ - D).map c = Z₀.map c - D.map c`. Use extensionality with `i j`.

Simplify using `[Matrix.map_apply]`. Rewrite using `[Matrix.transpose_sub, Matrix.sub_mul, hmap, Matrix.mul_sub, hDT, hDc]`. Establish `: E - u • E - u • E = 0`. Rewrite using `[sub_sub, ← add_smul, ← two_mul, mul_comm, hu, one_smul, sub_self]`. Rewrite using `[← this, hE]`.

Normalize the expressions using the abelian group laws. Introduce `i j`. Establish `: (Z₀ - D) i j - Z₀ i j = -(u * ∑ k, E j k * J⁻¹ k i)`. Simplify using `[hD, Matrix.transpose_apply, Matrix.mul_apply, Matrix.smul_apply, mul_comm]`. Rewrite using `[this]`.

Conclude with `neg_mem (Ideal.mul_mem_left _ _ (Ideal.sum_mem _ (fun k _ => Ideal.mul_mem_right _ _ (hZ j k))))`.
-/
theorem lift_mod_maximal_skew : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ Z₀ : Matrix (Fin n) (Fin n) O, (∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O) →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ ∀ i j, Z i j - Z₀ i j ∈ IsLocalRing.maximalIdeal O := by
  intro O _ _ c hc h2 n J hJ hdet Z₀ hZ
  obtain ⟨u, hu⟩ : ∃ u : O, u * 2 = 1 := ⟨h2.unit⁻¹.val, h2.val_inv_mul⟩
  have hcu : c u = u := by
    have h1 : c u * 2 = 1 := by
      have := congrArg c hu
      simpa [map_mul, map_ofNat] using this
    calc c u = c u * (u * 2) := by rw [hu, mul_one]
      _ = (c u * 2) * u := by ring
      _ = u := by rw [h1, one_mul]
  set E := Z₀ᵀ * J + J * Z₀.map c with hE
  have hJc : (J.map c)ᵀ = J := by
    ext i j; simp [Matrix.transpose_apply, Matrix.map_apply, hJ]
  have hEc : (E.map c)ᵀ = E := by
    ext i j
    simp only [hE, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add, map_sum, map_mul, hc, hJ]
    rw [add_comm]
    congr 1 <;> refine Finset.sum_congr rfl (fun k _ => ?_) <;> ring
  have hJinv : J * ((J⁻¹).map c)ᵀ = 1 := by
    calc J * ((J⁻¹).map c)ᵀ = (J.map c)ᵀ * ((J⁻¹).map c)ᵀ := by rw [hJc]
      _ = ((J⁻¹).map c * J.map c)ᵀ := by rw [Matrix.transpose_mul]
      _ = ((J⁻¹ * J).map c)ᵀ := by rw [Matrix.map_mul]
      _ = 1 := by rw [Matrix.nonsing_inv_mul J hdet, Matrix.map_one c c.map_zero c.map_one, Matrix.transpose_one]
  set D := (u • (E * J⁻¹))ᵀ with hD
  have hDT : Dᵀ * J = u • E := by
    rw [hD, Matrix.transpose_transpose, Matrix.smul_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul J hdet, Matrix.mul_one]
  have hDmap : D.map c = u • (((J⁻¹).map c)ᵀ * (E.map c)ᵀ) := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hD]
    ext i j
    simp [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, map_sum, map_mul, hcu]
  have hDc : J * D.map c = u • E := by
    rw [hDmap, Matrix.mul_smul, ← Matrix.mul_assoc, hJinv, Matrix.one_mul, hEc]
  refine ⟨Z₀ - D, ?_, ?_⟩
  · have hmap : (Z₀ - D).map c = Z₀.map c - D.map c := by
      ext i j; simp [Matrix.map_apply]
    rw [Matrix.transpose_sub, Matrix.sub_mul, hmap, Matrix.mul_sub, hDT, hDc]
    have : E - u • E - u • E = 0 := by
      rw [sub_sub, ← add_smul, ← two_mul, mul_comm, hu, one_smul, sub_self]
    rw [← this, hE]; abel
  · intro i j
    have : (Z₀ - D) i j - Z₀ i j = -(u * ∑ k, E j k * J⁻¹ k i) := by
      simp [hD, Matrix.transpose_apply, Matrix.mul_apply, Matrix.smul_apply, mul_comm]
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.sum_mem _ (fun k _ => Ideal.mul_mem_right _ _ (hZ j k))))

end GlobalTheory
