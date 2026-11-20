import Mathlib
open scoped TensorProduct

namespace GlobalTheory

open TensorProduct in

/- English proof (translation)
Set `φ : H ⊗[K] H →ₐ[K] H` to `(Algebra.TensorProduct.lid K H).toAlgHom.comp (Algebra.TensorProduct.map (Bialgebra.counitAlgHom K H) (AlgHom.id K H))`. Establish `hφΔ : φ (Coalgebra.comul (R` using `K) u) = u := by`. Establish `e` using `congrArg (TensorProduct.lid K H) (Coalgebra.rTensor_counit_comul (R := K) u)`. Rewrite `e` using `[TensorProduct.lid_tmul, one_smul]`. Conclude with `e`.

Establish `hφuu : φ (u ⊗ₜ[K] u) = Coalgebra.counit (R` using `K) u • u := by`. Simplify using `[φ]`. Establish `hε : Coalgebra.counit (R` using `K) u ≠ 0 := by`. Introduce `h0`. Establish `e` using `congrArg φ h`.

Rewrite `e` using `[map_mul, hφΔ, hφuu, h0, zero_smul]`. Conclude with `hu ((hc.map φ).mul_right_eq_zero.mp e)`. Set `ψ : H ⊗[K] H →ₐ[K] H` to `Algebra.TensorProduct.lift (AlgHom.id K H) (HopfAlgebra.antipodeAlgHom K H) (fun _ _ => Commute.all _ _)`. Establish `hψΔ : ψ (Coalgebra.comul (R` using `K) u) = algebraMap K H (Coalgebra.counit (R := K) u) := by`. Rewrite using `[← HopfAlgebra.mul_antipode_lTensor_comul_apply (R := K) u]`.

Proceed by induction on `Coalgebra.comul (R := K) u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [ψ]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Establish `hψuu : ψ (u ⊗ₜ[K] u) = u * HopfAlgebra.antipode K u`.

Simplify using `[ψ]`. Establish `e` using `congrArg ψ h`. Rewrite `e` using `[map_mul, hψΔ, hψuu]`. Establish `hU : IsUnit (u * HopfAlgebra.antipode K u)`. Rewrite using `[← e]`.

Conclude with `(hc.map ψ).mul ((isUnit_iff_ne_zero.mpr hε).map (algebraMap K H))`. Conclude with `isUnit_of_mul_isUnit_left hU`.
-/
theorem isUnit_of_unit_mul_comul_eq_tmul_self (K H : Type) [Field K] [CommRing H] [HopfAlgebra K H]
    (c : H ⊗[K] H) (hc : IsUnit c) (u : H) (hu : u ≠ 0)
    (h : c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u) : IsUnit u := by

  let φ : H ⊗[K] H →ₐ[K] H :=
    (Algebra.TensorProduct.lid K H).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.counitAlgHom K H) (AlgHom.id K H))
  have hφΔ : φ (Coalgebra.comul (R := K) u) = u := by
    have e := congrArg (TensorProduct.lid K H) (Coalgebra.rTensor_counit_comul (R := K) u)
    rw [TensorProduct.lid_tmul, one_smul] at e
    exact e
  have hφuu : φ (u ⊗ₜ[K] u) = Coalgebra.counit (R := K) u • u := by
    simp [φ]
  have hε : Coalgebra.counit (R := K) u ≠ 0 := by
    intro h0
    have e := congrArg φ h
    rw [map_mul, hφΔ, hφuu, h0, zero_smul] at e
    exact hu ((hc.map φ).mul_right_eq_zero.mp e)

  let ψ : H ⊗[K] H →ₐ[K] H :=
    Algebra.TensorProduct.lift (AlgHom.id K H) (HopfAlgebra.antipodeAlgHom K H)
      (fun _ _ => Commute.all _ _)
  have hψΔ : ψ (Coalgebra.comul (R := K) u) = algebraMap K H (Coalgebra.counit (R := K) u) := by
    rw [← HopfAlgebra.mul_antipode_lTensor_comul_apply (R := K) u]
    induction Coalgebra.comul (R := K) u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [ψ]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hψuu : ψ (u ⊗ₜ[K] u) = u * HopfAlgebra.antipode K u := by
    simp [ψ]
  have e := congrArg ψ h
  rw [map_mul, hψΔ, hψuu] at e
  have hU : IsUnit (u * HopfAlgebra.antipode K u) := by
    rw [← e]
    exact (hc.map ψ).mul ((isUnit_iff_ne_zero.mpr hε).map (algebraMap K H))
  exact isUnit_of_mul_isUnit_left hU

end GlobalTheory
