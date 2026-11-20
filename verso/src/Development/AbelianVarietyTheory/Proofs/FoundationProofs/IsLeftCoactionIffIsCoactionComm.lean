import Mathlib

open TensorProduct Coalgebra

namespace GlobalTheory

variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type*} [AddCommMonoid M] [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M']

structure IsCoaction (ρ : M →ₗ[R] M ⊗[R] C) : Prop where

  coassoc : ∀ m, TensorProduct.assoc R M C C (ρ.rTensor C (ρ m)) =
    (comul : C →ₗ[R] C ⊗[R] C).lTensor M (ρ m)

  counit : ∀ m, (counit : C →ₗ[R] R).lTensor M (ρ m) = m ⊗ₜ[R] (1 : R)

structure IsLeftCoaction (ρ : M →ₗ[R] C ⊗[R] M) : Prop where

  coassoc : ∀ m, TensorProduct.assoc R C C M ((comul : C →ₗ[R] C ⊗[R] C).rTensor M (ρ m)) =
    ρ.lTensor C (ρ m)

  counit : ∀ m, (counit : C →ₗ[R] R).rTensor M (ρ m) = (1 : R) ⊗ₜ[R] m

variable (R C) in

/- English proof (translation)
The claim follows from `coassoc_apply m counit m := lTensor_counit_comul m`.
-/
theorem isCoaction_comul : IsCoaction (comul : C →ₗ[R] C ⊗[R] C) where
  coassoc m := coassoc_apply m
  counit m := lTensor_counit_comul m

variable (R C) in

/- English proof (translation)
The claim follows from `coassoc_apply m counit m := rTensor_counit_comul m`.
-/
theorem isLeftCoaction_comul : IsLeftCoaction (comul : C →ₗ[R] C ⊗[R] C) where
  coassoc m := coassoc_apply m
  counit m := rTensor_counit_comul m

variable (M) in

/- English proof (translation)
Simplify using `[hg.comul_eq_tmul_self] counit m := by simp [hg.counit_eq_one]`.
-/
theorem isCoaction_of_isGroupLikeElem {g : C} (hg : IsGroupLikeElem R g) :
    IsCoaction ((TensorProduct.mk R M C).flip g) where
  coassoc m := by simp [hg.comul_eq_tmul_self]
  counit m := by simp [hg.counit_eq_one]

/- English proof (translation)
Simplify using `[h.counit]`.
-/
theorem IsCoaction.rid_counit {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) (m : M) :
    TensorProduct.rid R M ((Coalgebra.counit : C →ₗ[R] R).lTensor M (ρ m)) = m := by
  simp [h.counit]

/- English proof (translation)
The claim follows from `Function.LeftInverse.injective (g := fun t => TensorProduct.rid R M ((Coalgebra.counit : C →ₗ[R] R).lTensor M t)) h.rid_counit`.
-/
theorem IsCoaction.injective {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) : Function.Injective ρ :=
  Function.LeftInverse.injective
    (g := fun t => TensorProduct.rid R M ((Coalgebra.counit : C →ₗ[R] R).lTensor M t))
    h.rid_counit

/- English proof (translation)
Set `e : C ⊗[R] (C ⊗[R] M) ≃ₗ[R] M ⊗[R] (C ⊗[R] C)` to `(TensorProduct.assoc R C C M).symm ≪≫ₗ TensorProduct.comm R _ _ ≪≫ₗ (TensorProduct.comm R C C).lTensor M`. Establish `h1 : ∀ t : C ⊗[R] M, e (ρ.lTensor C t) = TensorProduct.assoc R M C C (((TensorProduct.comm R C M).toLinearMap ∘ₗ ρ).rTensor C (TensorProduct.comm R C M t))`. Introduce `t`. Proceed by induction on `t with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul c m`. Simplify using `only [LinearMap.lTensor_tmul, comm_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Generalize the expression as in `ρ m = s`. Proceed by induction on `s with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, tmul_add, add_tmul, ha, hb]`. Consider the case `tmul c' m' => simp [e]`. Establish `h2 : ∀ t : C ⊗[R] M, e (TensorProduct.assoc R C C M ((comul : C →ₗ[R] C ⊗[R] C).rTensor M t)) = (comul : C →ₗ[R] C ⊗[R] C).lTensor M (TensorProduct.comm R C M t)`. Introduce `t`.

Proceed by induction on `t with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul c m => simp [e]`. Establish `h3 : ∀ t : C ⊗[R] M, TensorProduct.comm R R M ((Coalgebra.counit : C →ₗ[R] R).rTensor M t) = (Coalgebra.counit : C →ₗ[R] R).lTensor M (TensorProduct.comm R C M t)`.

Introduce `t`. Proceed by induction on `t with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul c m => simp`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun m => ?_, fun m => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[← h1, ← h2, h.coassoc]`.

Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[← h3, h.counit, comm_tmul]`. Introduce `h`. Use `⟨fun m => e.injective ?_, fun m => (TensorProduct.comm R R M).injective ?_⟩` and prove the remaining obligations. Rewrite using `[h1, h2]`.

Conclude with `(h.coassoc m).symm`. Rewrite using `[h3, comm_tmul]`. Conclude with `h.counit m`.
-/
theorem isLeftCoaction_iff_isCoaction_comm [IsCocomm R C] (ρ : M →ₗ[R] C ⊗[R] M) :
    IsLeftCoaction ρ ↔ IsCoaction ((TensorProduct.comm R C M).toLinearMap ∘ₗ ρ) := by

  let e : C ⊗[R] (C ⊗[R] M) ≃ₗ[R] M ⊗[R] (C ⊗[R] C) :=
    (TensorProduct.assoc R C C M).symm ≪≫ₗ TensorProduct.comm R _ _ ≪≫ₗ
      (TensorProduct.comm R C C).lTensor M
  have h1 : ∀ t : C ⊗[R] M, e (ρ.lTensor C t) = TensorProduct.assoc R M C C
      (((TensorProduct.comm R C M).toLinearMap ∘ₗ ρ).rTensor C (TensorProduct.comm R C M t)) := by
    intro t
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m =>
      simp only [LinearMap.lTensor_tmul, comm_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply,
        LinearEquiv.coe_coe]
      generalize ρ m = s
      induction s with
      | zero => simp
      | add a b ha hb => simp only [map_add, tmul_add, add_tmul, ha, hb]
      | tmul c' m' => simp [e]
  have h2 : ∀ t : C ⊗[R] M,
      e (TensorProduct.assoc R C C M ((comul : C →ₗ[R] C ⊗[R] C).rTensor M t)) =
      (comul : C →ₗ[R] C ⊗[R] C).lTensor M (TensorProduct.comm R C M t) := by
    intro t
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m => simp [e]
  have h3 : ∀ t : C ⊗[R] M, TensorProduct.comm R R M ((Coalgebra.counit : C →ₗ[R] R).rTensor M t) =
      (Coalgebra.counit : C →ₗ[R] R).lTensor M (TensorProduct.comm R C M t) := by
    intro t
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m => simp
  constructor
  · intro h
    refine ⟨fun m => ?_, fun m => ?_⟩
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← h1, ← h2, h.coassoc]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← h3, h.counit, comm_tmul]
  · intro h
    refine ⟨fun m => e.injective ?_, fun m => (TensorProduct.comm R R M).injective ?_⟩
    · rw [h1, h2]; exact (h.coassoc m).symm
    · rw [h3, comm_tmul]; exact h.counit m

def coactionWeightSpace (ρ : M →ₗ[R] M ⊗[R] C) (g : C) : Submodule R M :=
  LinearMap.eqLocus ρ ((TensorProduct.mk R M C).flip g)

omit [Coalgebra R C] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
@[simp] theorem mem_coactionWeightSpace {ρ : M →ₗ[R] M ⊗[R] C} {g : C} {m : M} :
    m ∈ coactionWeightSpace ρ g ↔ ρ m = m ⊗ₜ[R] g := Iff.rfl

omit [Coalgebra R C] in

/- English proof (translation)
Rewrite `hm`, the goal using `[mem_coactionWeightSpace]`. Rewrite using `[hf, hm, LinearMap.rTensor_tmul]`.
-/
theorem map_mem_coactionWeightSpace {ρ : M →ₗ[R] M ⊗[R] C} {ρ' : M' →ₗ[R] M' ⊗[R] C}
    {f : M →ₗ[R] M'} (hf : ∀ m, ρ' (f m) = f.rTensor C (ρ m)) {g : C} {m : M}
    (hm : m ∈ coactionWeightSpace ρ g) : f m ∈ coactionWeightSpace ρ' g := by
  rw [mem_coactionWeightSpace] at hm ⊢
  rw [hf, hm, LinearMap.rTensor_tmul]

end GlobalTheory
