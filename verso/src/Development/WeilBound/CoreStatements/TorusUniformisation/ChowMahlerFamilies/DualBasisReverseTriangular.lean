import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace PositivityTheory.Xgn.DualReverseTriangular

/- English proof (translation)
Use `conv_rhs => rw [← v.sum_repr z]`. Rewrite using `[dotProduct_sum]`. Simplify using `only [dotProduct_smul, h, Fin.rev_inj, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem repr_eq_dot {Ω : Type} [Field Ω] {r : ℕ} (w v : Module.Basis (Fin r) Ω (Fin r → Ω))
    (h : ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0) (z : Fin r → Ω) (j : Fin r) :
    v.repr z j = w j.rev ⬝ᵥ z := by
  conv_rhs => rw [← v.sum_repr z]
  rw [dotProduct_sum]
  simp only [dotProduct_smul, h, Fin.rev_inj, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

/- English proof (translation)
Use `conv_rhs => rw [← w.sum_repr z]`. Rewrite using `[sum_dotProduct]`. Simplify using `only [smul_dotProduct, h, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem repr_eq_dot' {Ω : Type} [Field Ω] {r : ℕ} (w v : Module.Basis (Fin r) Ω (Fin r → Ω))
    (h : ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0) (z : Fin r → Ω) (j : Fin r) :
    w.repr z j.rev = z ⬝ᵥ v j := by
  conv_rhs => rw [← w.sum_repr z]
  rw [sum_dotProduct]
  simp only [smul_dotProduct, h, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

/- English proof (translation)
Establish `hAB` using `w.toMatrix_mul_toMatrix_flip w'`. Establish `hBA` using `w'.toMatrix_mul_toMatrix_flip w`. Use `letI : Invertible (w.toMatrix w') := ⟨w'.toMatrix w, hBA, hAB⟩`. Establish `hA : (w.toMatrix w').BlockTriangular id`. Introduce `i j hji`.

Rewrite using `[Module.Basis.toMatrix_apply]`. Conclude with `h j i hji`. Establish `hB : (w'.toMatrix w).BlockTriangular id`. Establish `hinv` using `Matrix.blockTriangular_inv_of_blockTriangular hA`. Rewrite `hinv` using `[Matrix.inv_eq_right_inv hAB]`. Then use the resulting hypothesis.

Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Simplify `hB hij` using `[Module.Basis.toMatrix_apply]`. Establish `e` using `congrFun (congrFun hBA i) i`. Rewrite `e` using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Simplify `e` using `[Module.Basis.toMatrix_apply]`.

Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with hlt | hlt` into its components or cases. Rewrite using `[hB hlt, zero_mul]`. Rewrite using `[hA hlt, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem tri_inv {Ω : Type} [Field Ω] {r : ℕ} (w w' : Module.Basis (Fin r) Ω (Fin r → Ω))
    (h : ∀ i j, i < j → w.repr (w' i) j = 0) :
    (∀ i j, i < j → w'.repr (w i) j = 0) ∧ ∀ i, w'.repr (w i) i * w.repr (w' i) i = 1 := by
  have hAB := w.toMatrix_mul_toMatrix_flip w'
  have hBA := w'.toMatrix_mul_toMatrix_flip w
  letI : Invertible (w.toMatrix w') := ⟨w'.toMatrix w, hBA, hAB⟩
  have hA : (w.toMatrix w').BlockTriangular id := by
    intro i j hji
    rw [Module.Basis.toMatrix_apply]
    exact h j i hji
  have hB : (w'.toMatrix w).BlockTriangular id := by
    have hinv := Matrix.blockTriangular_inv_of_blockTriangular hA
    rwa [Matrix.inv_eq_right_inv hAB] at hinv
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · simpa [Module.Basis.toMatrix_apply] using hB hij
  · have e := congrFun (congrFun hBA i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at e
    · simpa [Module.Basis.toMatrix_apply] using e
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hlt | hlt
      · rw [hB hlt, zero_mul]
      · rw [hA hlt, mul_zero]
    · simp

end PositivityTheory.Xgn.DualReverseTriangular

/- English proof (translation)
Introduce `Ω _ r w w' v v' h h' ht`. Take `⟨h1, h2⟩` from `PositivityTheory.Xgn.DualReverseTriangular.tri_inv w w' ht`. Establish `key : ∀ i j, v.repr (v' i) j = w'.repr (w j.rev) i.rev` using `fun i j => by`. Rewrite using `[PositivityTheory.Xgn.DualReverseTriangular.repr_eq_dot w v h, PositivityTheory.Xgn.DualReverseTriangular.repr_eq_dot' w' v' h']`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[key]`. Conclude with `h1 _ _ (Fin.rev_lt_rev.mpr hij)`. Rewrite using `[key]`. Conclude with `h2 _`.
-/
theorem PositivityTheory.Xgn.dual_basis_reverse_triangular : ∀ (Ω : Type) [Field Ω] (r : ℕ) (w w' v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
    (∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0) → (∀ i j, w' i ⬝ᵥ v' j = if i = j.rev then 1 else 0) →
    (∀ i j, i < j → w.repr (w' i) j = 0) →
    (∀ i j, i < j → v.repr (v' i) j = 0) ∧ ∀ i, v.repr (v' i) i * w.repr (w' i.rev) i.rev = 1 := by
  intro Ω _ r w w' v v' h h' ht
  obtain ⟨h1, h2⟩ := PositivityTheory.Xgn.DualReverseTriangular.tri_inv w w' ht
  have key : ∀ i j, v.repr (v' i) j = w'.repr (w j.rev) i.rev := fun i j => by
    rw [PositivityTheory.Xgn.DualReverseTriangular.repr_eq_dot w v h,
      PositivityTheory.Xgn.DualReverseTriangular.repr_eq_dot' w' v' h']
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key]
    exact h1 _ _ (Fin.rev_lt_rev.mpr hij)
  · rw [key]
    exact h2 _
