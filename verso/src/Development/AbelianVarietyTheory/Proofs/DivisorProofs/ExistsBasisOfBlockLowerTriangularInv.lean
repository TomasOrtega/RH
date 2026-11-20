import Mathlib

namespace GlobalTheory

open Matrix

/- English proof (translation)
Establish `hAA : P.toBlocks₁₁ * P'.toBlocks₁₁ = 1`. Use extensionality with `i i'`. Use `congrFun (congrFun h1 (Sum.inl i)) (Sum.inl i')` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₁₁]`. Establish `hA'A : P'.toBlocks₁₁ * P.toBlocks₁₁ = 1` using `mul_eq_one_comm.mp hAA`.

Establish `hAB : P.toBlocks₁₁ * P'.toBlocks₁₂ = 0`. Use extensionality with `i j`. Use `congrFun (congrFun h1 (Sum.inl i)) (Sum.inr j)` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]`. Establish `hB : P'.toBlocks₁₂ = 0`.

Combine the equalities or inequalities in the displayed calculation. Establish `hb : ∀ a j, P' (Sum.inl a) (Sum.inr j) = 0` using `fun a j => by`. Simplify `congrFun (congrFun hB a) j` using `[Matrix.toBlocks₁₂]`. Establish `hDD : P.toBlocks₂₂ * P'.toBlocks₂₂ = 1`. Use extensionality with `j j2`.

Use `congrFun (congrFun h1 (Sum.inr j)) (Sum.inr j2)` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Fintype.sum_sum_type, hb, Matrix.one_apply, Matrix.toBlocks₂₂]`. Establish `hD'D : P'.toBlocks₂₂ * P.toBlocks₂₂ = 1`. Use extensionality with `j j2`. Use `congrFun (congrFun h2 (Sum.inr j)) (Sum.inr j2)` as an intermediate fact.

Simplify `this` using `[Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₂₂]`. Use `set D := P.toBlocks₂₂ with hDdef`. Use `set D' := P'.toBlocks₂₂`. Set `L : (Fin k → O) ≃ₗ[O] (Fin k' → O)` to `LinearEquiv.ofLinear (Matrix.toLin' Dᵀ) (Matrix.toLin' D'ᵀ) (by rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, hD'D, Matrix.transpose_one, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, hDD, Matrix.transpose_one, Matrix.toLin'_one])`. Use `⟨Module.Basis.ofEquivFun (lbs.equivFun.trans L.symm), fun j => ?_⟩` and prove the remaining obligations.

Rewrite using `[Module.Basis.coe_ofEquivFun]`. Simplify using `only [LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, Module.Basis.equivFun_symm_apply]`. Use `Finset.sum_congr rfl fun j' _ => ?_` and prove the remaining obligations. Use `congr 1`. Simplify using `[L, Matrix.mulVec, dotProduct, Pi.single_apply, hDdef, Matrix.toBlocks₂₂]`.
-/
theorem exists_basis_of_blockLowerTriangular_inv (O M : Type) [CommRing O] [AddCommGroup M] [Module O M]
    (d k k' : ℕ) (lbs : Module.Basis (Fin k') O M)
    (P : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k') O) (P' : Matrix (Fin d ⊕ Fin k') (Fin d ⊕ Fin k) O)
    (h1 : P * P' = 1) (h2 : P' * P = 1) (hz : ∀ i j, P (Sum.inl i) (Sum.inr j) = 0) :
    ∃ lb : Module.Basis (Fin k) O M, ∀ j, lb j = ∑ j', P (Sum.inr j) (Sum.inr j') • lbs j' := by
  have hAA : P.toBlocks₁₁ * P'.toBlocks₁₁ = 1 := by
    ext i i'
    have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inl i')
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₁₁] using this
  have hA'A : P'.toBlocks₁₁ * P.toBlocks₁₁ = 1 := mul_eq_one_comm.mp hAA
  have hAB : P.toBlocks₁₁ * P'.toBlocks₁₂ = 0 := by
    ext i j
    have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inr j)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂] using this
  have hB : P'.toBlocks₁₂ = 0 := by
    calc P'.toBlocks₁₂ = (P'.toBlocks₁₁ * P.toBlocks₁₁) * P'.toBlocks₁₂ := by rw [hA'A, Matrix.one_mul]
      _ = P'.toBlocks₁₁ * (P.toBlocks₁₁ * P'.toBlocks₁₂) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hAB, Matrix.mul_zero]
  have hb : ∀ a j, P' (Sum.inl a) (Sum.inr j) = 0 := fun a j => by
    simpa [Matrix.toBlocks₁₂] using congrFun (congrFun hB a) j
  have hDD : P.toBlocks₂₂ * P'.toBlocks₂₂ = 1 := by
    ext j j2
    have := congrFun (congrFun h1 (Sum.inr j)) (Sum.inr j2)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hb, Matrix.one_apply, Matrix.toBlocks₂₂] using this
  have hD'D : P'.toBlocks₂₂ * P.toBlocks₂₂ = 1 := by
    ext j j2
    have := congrFun (congrFun h2 (Sum.inr j)) (Sum.inr j2)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₂₂] using this
  set D := P.toBlocks₂₂ with hDdef
  set D' := P'.toBlocks₂₂
  let L : (Fin k → O) ≃ₗ[O] (Fin k' → O) :=
    LinearEquiv.ofLinear (Matrix.toLin' Dᵀ) (Matrix.toLin' D'ᵀ)
      (by rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, hD'D, Matrix.transpose_one, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, hDD, Matrix.transpose_one, Matrix.toLin'_one])
  refine ⟨Module.Basis.ofEquivFun (lbs.equivFun.trans L.symm), fun j => ?_⟩
  rw [Module.Basis.coe_ofEquivFun]
  simp only [LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, Module.Basis.equivFun_symm_apply]
  refine Finset.sum_congr rfl fun j' _ => ?_
  congr 1
  simp [L, Matrix.mulVec, dotProduct, Pi.single_apply, hDdef, Matrix.toBlocks₂₂]

end GlobalTheory
