import Mathlib

open TensorProduct

namespace GlobalTheory.LeftRightDerivations

variable {k : Type*} {H : Type*} [CommSemiring k] [CommSemiring H] [Bialgebra k H]

def IsCounitDerivation (φ : H →ₗ[k] k) : Prop :=
  ∀ a b : H, φ (a * b) =
    Coalgebra.counit (R := k) a * φ b + Coalgebra.counit (R := k) b * φ a

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem isCounitDerivation_iff (φ : H →ₗ[k] k) :
    IsCounitDerivation φ ↔ ∀ a b : H, φ (a * b) =
      Coalgebra.counit (R := k) a * φ b + Coalgebra.counit (R := k) b * φ a := Iff.rfl

noncomputable def contrRight (φ : H →ₗ[k] k) : H ⊗[k] H →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap ∘ₗ LinearMap.lTensor H φ

noncomputable def contrLeft (φ : H →ₗ[k] k) : H ⊗[k] H →ₗ[k] H :=
  (TensorProduct.lid k H).toLinearMap ∘ₗ LinearMap.rTensor H φ

/- English proof (translation)
Simplify using `[contrRight]`.
-/
@[simp] theorem contrRight_tmul (φ : H →ₗ[k] k) (a b : H) :
    contrRight φ (a ⊗ₜ[k] b) = φ b • a := by
  simp [contrRight]

/- English proof (translation)
Simplify using `[contrLeft]`.
-/
@[simp] theorem contrLeft_tmul (φ : H →ₗ[k] k) (a b : H) :
    contrLeft φ (a ⊗ₜ[k] b) = φ a • b := by
  simp [contrLeft]

/- English proof (translation)
Simplify using `[contrRight, Coalgebra.lTensor_counit_comul]`.
-/
theorem contrRight_counit_comul (a : H) :
    contrRight (Coalgebra.counit (R := k)) (Coalgebra.comul (R := k) a) = a := by

  simp [contrRight, Coalgebra.lTensor_counit_comul]

/- English proof (translation)
Simplify using `[contrLeft, Coalgebra.rTensor_counit_comul]`.
-/
theorem contrLeft_counit_comul (a : H) :
    contrLeft (Coalgebra.counit (R := k)) (Coalgebra.comul (R := k) a) = a := by
  simp [contrLeft, Coalgebra.rTensor_counit_comul]

/- English proof (translation)
Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [add_mul, map_add, hx, hy]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `tmul a b`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [mul_add, map_add, hx, hy]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `tmul c d`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul]`. Simplify using `only [contrRight_tmul, hφ b d, Algebra.smul_def, map_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem contrRight_mul {φ : H →ₗ[k] k} (hφ : IsCounitDerivation φ) (s t : H ⊗[k] H) :
    contrRight φ (s * t) =
      contrRight (Coalgebra.counit (R := k)) s * contrRight φ t +
        contrRight (Coalgebra.counit (R := k)) t * contrRight φ s := by

  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]; ring
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]; ring
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp only [contrRight_tmul, hφ b d, Algebra.smul_def, map_add, map_mul]
      ring

/- English proof (translation)
Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [add_mul, map_add, hx, hy]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `tmul a b`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [mul_add, map_add, hx, hy]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `tmul c d`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul]`. Simplify using `only [contrLeft_tmul, hφ a c, Algebra.smul_def, map_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem contrLeft_mul {φ : H →ₗ[k] k} (hφ : IsCounitDerivation φ) (s t : H ⊗[k] H) :
    contrLeft φ (s * t) =
      contrLeft (Coalgebra.counit (R := k)) s * contrLeft φ t +
        contrLeft (Coalgebra.counit (R := k)) t * contrLeft φ s := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]; ring
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]; ring
    | tmul c d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp only [contrLeft_tmul, hφ a c, Algebra.smul_def, map_add, map_mul]
      ring

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.one_def, contrRight_tmul]`.
-/
theorem contrRight_one (φ : H →ₗ[k] k) : contrRight φ 1 = φ 1 • (1 : H) := by
  rw [Algebra.TensorProduct.one_def, contrRight_tmul]

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.one_def, contrLeft_tmul]`.
-/
theorem contrLeft_one (φ : H →ₗ[k] k) : contrLeft φ 1 = φ 1 • (1 : H) := by
  rw [Algebra.TensorProduct.one_def, contrLeft_tmul]

/- English proof (translation)
Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [mul_comm]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem counit_contrRight (φ : H →ₗ[k] k) (s : H ⊗[k] H) :
    Coalgebra.counit (R := k) (contrRight φ s) =
      φ (contrLeft (Coalgebra.counit (R := k)) s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [mul_comm]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem counit_contrLeft (φ : H →ₗ[k] k) (s : H ⊗[k] H) :
    Coalgebra.counit (R := k) (contrLeft φ s) =
      φ (contrRight (Coalgebra.counit (R := k)) s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

section Ring

variable {k : Type*} {H : Type*} [CommRing k] [CommRing H] [Bialgebra k H]

/- English proof (translation)
Establish `h` using `hφ 1 1`. Rewrite `h` using `[mul_one, Bialgebra.counit_one, one_mul]`. Simplify using `using h`.
-/
theorem IsCounitDerivation.map_one {φ : H →ₗ[k] k} (hφ : IsCounitDerivation φ) : φ 1 = 0 := by

  have h := hφ 1 1
  rw [mul_one, Bialgebra.counit_one, one_mul] at h
  simpa using h

noncomputable def derivRight (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) : Derivation k H H where
  toLinearMap := contrRight φ ∘ₗ Coalgebra.comul (R := k)
  map_one_eq_zero' := by
    rw [LinearMap.comp_apply, Bialgebra.comul_one, contrRight_one, hφ.map_one, zero_smul]
  leibniz' a b := by
    simp only [LinearMap.comp_apply, Bialgebra.comul_mul, contrRight_mul hφ,
      contrRight_counit_comul, smul_eq_mul]

noncomputable def derivLeft (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) : Derivation k H H where
  toLinearMap := contrLeft φ ∘ₗ Coalgebra.comul (R := k)
  map_one_eq_zero' := by
    rw [LinearMap.comp_apply, Bialgebra.comul_one, contrLeft_one, hφ.map_one, zero_smul]
  leibniz' a b := by
    simp only [LinearMap.comp_apply, Bialgebra.comul_mul, contrLeft_mul hφ,
      contrLeft_counit_comul, smul_eq_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem derivRight_apply (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) (y : H) :
    derivRight φ hφ y =
      TensorProduct.rid k H (LinearMap.lTensor H φ (Coalgebra.comul (R := k) y)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem derivLeft_apply (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) (y : H) :
    derivLeft φ hφ y =
      TensorProduct.lid k H (LinearMap.rTensor H φ (Coalgebra.comul (R := k) y)) := rfl

/- English proof (translation)
Establish `h : derivRight φ hφ y = contrRight φ (Coalgebra.comul (R` using `k) y) := rfl`. Rewrite using `[h, counit_contrRight, contrLeft_counit_comul]`.
-/
theorem counit_derivRight (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) (y : H) :
    Coalgebra.counit (R := k) (derivRight φ hφ y) = φ y := by
  have h : derivRight φ hφ y = contrRight φ (Coalgebra.comul (R := k) y) := rfl
  rw [h, counit_contrRight, contrLeft_counit_comul]

/- English proof (translation)
Establish `h : derivLeft φ hφ y = contrLeft φ (Coalgebra.comul (R` using `k) y) := rfl`. Rewrite using `[h, counit_contrLeft, contrRight_counit_comul]`.
-/
theorem counit_derivLeft (φ : H →ₗ[k] k) (hφ : IsCounitDerivation φ) (y : H) :
    Coalgebra.counit (R := k) (derivLeft φ hφ y) = φ y := by
  have h : derivLeft φ hφ y = contrLeft φ (Coalgebra.comul (R := k) y) := rfl
  rw [h, counit_contrLeft, contrRight_counit_comul]

/- English proof (translation)
Introduce `a b`. Simplify using `[Derivation.leibniz, Bialgebra.counit_mul]`.
-/
theorem isCounitDerivation_counit_comp (D : Derivation k H H) :
    IsCounitDerivation (Coalgebra.counit (R := k) ∘ₗ D.toLinearMap) := by

  intro a b
  simp [Derivation.leibniz, Bialgebra.counit_mul]

end Ring

end GlobalTheory.LeftRightDerivations
