import Mathlib

noncomputable section

open scoped TensorProduct Matrix

namespace PositivityTheory.Rg.Cz

section
variable {V : Type} [AddCommGroup V] [Module ℂ V] {d : ℕ}
  (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (B : (V ⊗[ℂ] (Fin d → ℂ)) →ₗ[ℂ] (V ⊗[ℂ] (Fin d → ℂ)) →ₗ⋆[ℂ] ℂ)

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x x' hx hx' => simp only [map_add, LinearMap.add_apply]`. Take the linear combination `hx + hx'`. Consider the case `tmul φ v`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add y y' hy hy' => simp only [map_add]`. Take the linear combination `hy + hy'`. Consider the case `tmul ψ w`.

Simplify using `only [LinearMap.rTensor_tmul, hB]`. Take the linear combination `(star w ⬝ᵥ v) * hA ψ φ`.
-/
theorem kg_form_rTensor (hB : ∀ φ ψ v w, B (φ ⊗ₜ v) (ψ ⊗ₜ w) = H ψ φ * (star w ⬝ᵥ v))
    (A : V →ₗ[ℂ] V) (s : ℂ) (hA : ∀ φ ψ, H (A φ) ψ + H φ (A ψ) = s * H φ ψ) (x y : V ⊗[ℂ] (Fin d → ℂ)) :
    B (A.rTensor _ x) y + B x (A.rTensor _ y) = s * B x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply]; linear_combination hx + hx'
  | tmul φ v =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add]; linear_combination hy + hy'
    | tmul ψ w =>
      simp only [LinearMap.rTensor_tmul, hB]
      linear_combination (star w ⬝ᵥ v) * hA ψ φ

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']`. Consider the case `tmul φ v`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add y y' hy hy' => simp only [map_add, hy, hy']`. Consider the case `tmul ψ w`. Simplify using `only [LinearMap.lTensor_tmul, hB, Matrix.toLin'_apply]`. Rewrite using `[Matrix.star_mulVec, hD, ← Matrix.dotProduct_mulVec]`.
-/
theorem kg_form_lTensor (hB : ∀ φ ψ v w, B (φ ⊗ₜ v) (ψ ⊗ₜ w) = H ψ φ * (star w ⬝ᵥ v))
    (D : Matrix (Fin d) (Fin d) ℂ) (hD : Dᴴ = D) (x y : V ⊗[ℂ] (Fin d → ℂ)) :
    B ((Matrix.toLin' D).lTensor V x) y = B x ((Matrix.toLin' D).lTensor V y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul φ v =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul ψ w =>
      simp only [LinearMap.lTensor_tmul, hB, Matrix.toLin'_apply]
      rw [Matrix.star_mulVec, hD, ← Matrix.dotProduct_mulVec]

end

/- English proof (translation)
Establish `e : B (((2 : ℂ) • ∑ i, (f i - (c i : ℂ) • 1)) x) x = 2 * ∑ i, (B (f i x) x - (c i : ℂ) * B x x)`. Simplify using `only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_sum, map_sub, smul_eq_mul]`. Rewrite using `[e, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul, Complex.re_sum]`. Use `mul_nonpos_of_nonneg_of_nonpos (by norm_num) (Finset.sum_nonpos fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Complex.sub_re, Complex.re_ofReal_mul]`.

Combine the linear relations using `[h i x]`.
-/
theorem kg_re_le {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) {ι : Type} [Fintype ι]
    (f : ι → Module.End ℂ V) (c : ι → ℝ) (h : ∀ i x, (B (f i x) x).re ≤ c i * (B x x).re) (x : V) :
    (B (((2 : ℂ) • ∑ i, (f i - (c i : ℂ) • 1)) x) x).re ≤ 0 := by
  have e : B (((2 : ℂ) • ∑ i, (f i - (c i : ℂ) • 1)) x) x = 2 * ∑ i, (B (f i x) x - (c i : ℂ) * B x x) := by
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_smul, map_sum, map_sub, smul_eq_mul]
  rw [e, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul, Complex.re_sum]
  refine mul_nonpos_of_nonneg_of_nonpos (by norm_num) (Finset.sum_nonpos fun i _ => ?_)
  rw [Complex.sub_re, Complex.re_ofReal_mul]
  linarith [h i x]

/- English proof (translation)
Establish `h : ∀ i j, (F i j + (if i = j then x else 0) • (1 : A)) * (F j i + (if j = i then x else 0) • (1 : A)) = F i j * F j i + if i = j then (2 * x) • F i i + (x ^ 2) • (1 : A) else 0`. Introduce `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `only [if_true, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]`.

Use `module`. Simplify using `[hij, Ne.symm hij]`. Simplify using `only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.smul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem kg_cas_shift {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) (x : ℂ) :
    ∑ i, ∑ j, (F i j + (if i = j then x else 0) • (1 : A)) * (F j i + (if j = i then x else 0) • (1 : A)) =
      ∑ i, ∑ j, F i j * F j i + (2 * x) • ∑ i, F i i + ((n : ℂ) * x ^ 2) • (1 : A) := by
  have h : ∀ i j, (F i j + (if i = j then x else 0) • (1 : A)) * (F j i + (if j = i then x else 0) • (1 : A)) =
      F i j * F j i + if i = j then (2 * x) • F i i + (x ^ 2) • (1 : A) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [if_true, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    · simp [hij, Ne.symm hij]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.smul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  abel
