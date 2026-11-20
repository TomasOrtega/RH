import Mathlib

open TensorProduct

namespace GlobalTheory

open TensorProduct in

/- English proof (translation)
Establish `hB : (Algebra.traceForm F K).Nondegenerate` using `traceForm_nondegenerate F K`. Establish `hsymm : (Algebra.traceForm F K).IsSymm` using `Algebra.traceForm_isSymm F`. Set `b` to `Module.finBasis F K`. Set `d` to `(Algebra.traceForm F K).dualBasis hB b`. Establish `hbd : ∀ i j, Algebra.trace F K (b i * d j) = if i = j then 1 else 0` using `fun i j => by`.

Rewrite using `[← Algebra.traceForm_apply]`. Conclude with `LinearMap.BilinForm.apply_dualBasis_right hB hsymm b i j`. Use `set s : K := ∑ j, b j * d j with hs`. Establish `hd : ∀ x : K, ∑ i, Algebra.trace F K (x * b i) • d i = x`. Introduce `x`.

Use `conv_rhs => rw [← d.sum_repr x]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]`. Establish `hb : ∀ x : K, ∑ j, Algebra.trace F K (x * d j) • b j = x`. Introduce `x`.

Use `conv_rhs => rw [← b.sum_repr x]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 1`. Use `conv_lhs => rw [← b.sum_repr x]`. Rewrite using `[Finset.sum_mul, map_sum]`.

Simplify using `[smul_mul_assoc, hbd]`. Establish `hs0 : s ≠ 0`. Introduce `h`. Establish `htr : Algebra.trace F K s = (Module.finrank F K : F)`. Rewrite using `[hs, map_sum]`.

Simplify using `[hbd]`. Rewrite `htr` using `[h, map_zero]`. Conclude with `(Module.finrank_pos (R := F) (M := K)).ne' (Nat.cast_eq_zero.mp htr.symm)`. Use `⟨Module.finrank F K, fun j => τ (s⁻¹ * b j), d, ?_, fun y => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [← map_mul, ← map_sum, hs, Finset.mul_sum, mul_assoc]`. Use `_ = 1 := by rw [inv_mul_cancel₀ hs0, map_one]`. Establish `lhs : ∑ j, τ (s⁻¹ * b j) ⊗ₜ[F] (y * d j) = ∑ j, ∑ i, (Algebra.trace F K (y * d j * b i) • τ (s⁻¹ * b j)) ⊗ₜ[F] d i`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `conv_lhs => rw [← hd (y * d j)]`.

Rewrite using `[TensorProduct.tmul_sum]`. Repeatedly rewrite using `[TensorProduct.tmul_smul, TensorProduct.smul_tmul']`. Establish `rhs : ∑ i, (τ y * τ (s⁻¹ * b i)) ⊗ₜ[F] d i = ∑ i, ∑ j, (Algebra.trace F K (y * b i * d j) • τ (s⁻¹ * b j)) ⊗ₜ[F] d i`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← map_mul, mul_left_comm]`.

Use `conv_lhs => rw [← hb (y * b i)]`. Rewrite using `[Finset.mul_sum, map_sum, TensorProduct.sum_tmul]`. Repeatedly rewrite using `[mul_smul_comm, map_smul]`. Rewrite using `[lhs, rhs, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_right_comm y (d j) (b i)]`.
-/
theorem _root_.GlobalTheory.exists_embedding_idempotent_tensor (F K L : Type) [Field F] [CharZero F] [Field K]
    [Field L] [Algebra F K] [Algebra F L] [FiniteDimensional F K] (τ : K →ₐ[F] L) :
    ∃ (m : ℕ) (c : Fin m → L) (k : Fin m → K), ∑ j, c j * τ (k j) = 1 ∧
      ∀ y : K, ∑ j, c j ⊗ₜ[F] (y * k j) = ∑ j, (τ y * c j) ⊗ₜ[F] k j := by
  classical
  have hB : (Algebra.traceForm F K).Nondegenerate := traceForm_nondegenerate F K
  have hsymm : (Algebra.traceForm F K).IsSymm := Algebra.traceForm_isSymm F
  let b := Module.finBasis F K
  let d := (Algebra.traceForm F K).dualBasis hB b
  have hbd : ∀ i j, Algebra.trace F K (b i * d j) = if i = j then 1 else 0 := fun i j => by
    rw [← Algebra.traceForm_apply]
    exact LinearMap.BilinForm.apply_dualBasis_right hB hsymm b i j
  set s : K := ∑ j, b j * d j with hs
  have hd : ∀ x : K, ∑ i, Algebra.trace F K (x * b i) • d i = x := by
    intro x
    conv_rhs => rw [← d.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  have hb : ∀ x : K, ∑ j, Algebra.trace F K (x * d j) • b j = x := by
    intro x
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    conv_lhs => rw [← b.sum_repr x]
    rw [Finset.sum_mul, map_sum]
    simp [smul_mul_assoc, hbd]
  have hs0 : s ≠ 0 := by
    intro h
    have htr : Algebra.trace F K s = (Module.finrank F K : F) := by
      rw [hs, map_sum]
      simp [hbd]
    rw [h, map_zero] at htr
    exact (Module.finrank_pos (R := F) (M := K)).ne' (Nat.cast_eq_zero.mp htr.symm)
  refine ⟨Module.finrank F K, fun j => τ (s⁻¹ * b j), d, ?_, fun y => ?_⟩
  · calc ∑ j, τ (s⁻¹ * b j) * τ (d j) = τ (s⁻¹ * s) := by
          simp only [← map_mul, ← map_sum, hs, Finset.mul_sum, mul_assoc]
      _ = 1 := by rw [inv_mul_cancel₀ hs0, map_one]
  · have lhs : ∑ j, τ (s⁻¹ * b j) ⊗ₜ[F] (y * d j) =
        ∑ j, ∑ i, (Algebra.trace F K (y * d j * b i) • τ (s⁻¹ * b j)) ⊗ₜ[F] d i := by
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_lhs => rw [← hd (y * d j)]
      rw [TensorProduct.tmul_sum]
      simp_rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    have rhs : ∑ i, (τ y * τ (s⁻¹ * b i)) ⊗ₜ[F] d i =
        ∑ i, ∑ j, (Algebra.trace F K (y * b i * d j) • τ (s⁻¹ * b j)) ⊗ₜ[F] d i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← map_mul, mul_left_comm]
      conv_lhs => rw [← hb (y * b i)]
      rw [Finset.mul_sum, map_sum, TensorProduct.sum_tmul]
      simp_rw [mul_smul_comm, map_smul]
    rw [lhs, rhs, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_right_comm y (d j) (b i)]

end GlobalTheory
