import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

namespace GlobalTheory.LocIso

/- English proof (translation)
Introduce `O _ _ _ ℓ _`. Set `g1 : O →ₐ[ℤ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)` to `((Algebra.TensorProduct.includeRight : (ℚ ⊗[ℤ] O) →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)).toRingHom.comp (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom).toIntAlgHom`. Set `g2 : ℤ_[ℓ] →ₐ[ℤ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)` to `((Algebra.TensorProduct.includeLeftRingHom (R := ℚ) (A := ℚ_[ℓ]) (B := ℚ ⊗[ℤ] O)).comp PadicInt.Coe.ringHom).toIntAlgHom`. Establish `hg1 : ∀ x, g1 x = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x)` using `fun _ => rfl`. Establish `hg2 : ∀ y : ℤ_[ℓ], g2 y = (y : ℚ_[ℓ]) ⊗ₜ[ℚ] (1 : ℚ ⊗[ℤ] O)` using `fun _ => rfl`.

Establish `hg : ∀ x y, Commute (g1 x) (g2 y)`. Introduce `x y`. Simplify using `only [hg1, hg2, Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Set `f` to `Algebra.TensorProduct.lift g1 g2 hg`. Establish `hf : ∀ (o : O) (a : ℤ_[ℓ]), f (o ⊗ₜ a) = (a : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o)`.

Introduce `o a`. Simplify using `only [f, Algebra.TensorProduct.lift_tmul, hg1, hg2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Establish `hinj : Function.Injective f`. Establish `hl : Function.Injective (LinearMap.lTensor O (PadicInt.Coe.ringHom (p` using `ℓ)).toIntAlgHom.toLinearMap) := Module.Flat.lTensor_preserves_injective_linearMap _ (fun a b h => Subtype.ext h)`. Establish `heq : (f : O ⊗[ℤ] ℤ_[ℓ] → ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) = (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℚ_[ℓ] ℚ_[ℓ] O).symm ∘ (TensorProduct.comm ℤ O ℚ_[ℓ]) ∘ (LinearMap.lTensor O (PadicInt.Coe.ringHom (p` using `ℓ)).toIntAlgHom.toLinearMap) := by`.

Use function extensionality and compare the values at `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul o a`. Simplify using `only [Function.comp_apply, LinearMap.lTensor_tmul, TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, hf]`.

Both sides reduce to the same expression. Consider the case `add x y hx hy`. Simplify using `only [Function.comp_apply, map_add] at hx hy ⊢`. Rewrite using `[hx, hy]`. Rewrite using `[heq]`.

Conclude with `(LinearEquiv.injective _).comp ((LinearEquiv.injective _).comp hl)`. Establish `hmem : ∀ x, f x ∈ locOrder ℓ (Algebra.TensorProduct.includeRight (R` using `ℤ) (A := ℚ) (B := O)).toRingHom.range := by`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul o a`. Rewrite using `[hf]`. Establish `h1 : (a : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) = algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) a * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o))`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Both sides reduce to the same expression.

Rewrite using `[h1]`. Use `Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) (Algebra.subset_adjoin ?_)` and prove the remaining obligations. Conclude with `⟨(1 : ℚ) ⊗ₜ[ℤ] o, ⟨o, rfl⟩, rfl⟩`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Subalgebra.add_mem _ hx hy`.

Set `g : O ⊗[ℤ] ℤ_[ℓ] →+* locOrder ℓ (Algebra.TensorProduct.includeRight (R` to `ℤ) (A := ℚ) (B := O)).toRingHom.range := (f.toRingHom).codRestrict _ hmem`. Establish `hsurj : Function.Surjective g`. Introduce and unpack `⟨y, hy⟩`. Establish `hy' : y ∈ (locOrder ℓ (Algebra.TensorProduct.includeRight (R` using `ℤ) (A := ℚ) (B := O)).toRingHom.range).toSubring := hy`. Rewrite `hy'` using `[locOrder, Algebra.adjoin_eq_ring_closure]`.

Establish `hle : Subring.closure (Set.range (algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O))) ∪ ((fun b => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) '' ((Algebra.TensorProduct.includeRight (R` using `ℤ) (A := ℚ) (B := O)).toRingHom.range : Set (ℚ ⊗[ℤ] O)))) ≤ f.toRingHom.range := by`. Rewrite using `[Subring.closure_le]`. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨_, ⟨o, rfl⟩, rfl⟩)`. Use `⟨(1 : O) ⊗ₜ a, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f _ = _`.

Rewrite using `[hf, Algebra.TensorProduct.algebraMap_apply]`. Both sides reduce to the same expression. Use `⟨o ⊗ₜ (1 : ℤ_[ℓ]), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f _ = _`. Rewrite using `[hf]`.

Simplify using the standard rewrite rules. Take `⟨x, hx⟩` from `hle hy'`. Conclude with `⟨x, Subtype.ext hx⟩`. Use `⟨RingEquiv.ofBijective g ⟨fun x y h => hinj (congrArg Subtype.val h), hsurj⟩, fun o => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f (o ⊗ₜ 1) = _`.

Rewrite using `[hf]`. Simplify using the standard rewrite rules.
-/
theorem tensor_padicInt_equiv_locOrder : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (ℓ : ℕ) [Fact ℓ.Prime], ∃ ι : O ⊗[ℤ] ℤ_[ℓ] ≃+* locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range, ∀ o : O, (ι (o ⊗ₜ[ℤ] 1) : ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) := by
  intro O _ _ _ ℓ _
  let g1 : O →ₐ[ℤ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O) :=
    ((Algebra.TensorProduct.includeRight : (ℚ ⊗[ℤ] O) →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom).toIntAlgHom
  let g2 : ℤ_[ℓ] →ₐ[ℤ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O) :=
    ((Algebra.TensorProduct.includeLeftRingHom (R := ℚ) (A := ℚ_[ℓ]) (B := ℚ ⊗[ℤ] O)).comp
      PadicInt.Coe.ringHom).toIntAlgHom
  have hg1 : ∀ x, g1 x = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) := fun _ => rfl
  have hg2 : ∀ y : ℤ_[ℓ], g2 y = (y : ℚ_[ℓ]) ⊗ₜ[ℚ] (1 : ℚ ⊗[ℤ] O) := fun _ => rfl
  have hg : ∀ x y, Commute (g1 x) (g2 y) := by
    intro x y
    simp only [hg1, hg2, Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  let f := Algebra.TensorProduct.lift g1 g2 hg
  have hf : ∀ (o : O) (a : ℤ_[ℓ]), f (o ⊗ₜ a) = (a : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) := by
    intro o a
    simp only [f, Algebra.TensorProduct.lift_tmul, hg1, hg2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have hinj : Function.Injective f := by
    have hl : Function.Injective (LinearMap.lTensor O (PadicInt.Coe.ringHom (p := ℓ)).toIntAlgHom.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (fun a b h => Subtype.ext h)
    have heq : (f : O ⊗[ℤ] ℤ_[ℓ] → ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) =
        (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℚ_[ℓ] ℚ_[ℓ] O).symm ∘
          (TensorProduct.comm ℤ O ℚ_[ℓ]) ∘
          (LinearMap.lTensor O (PadicInt.Coe.ringHom (p := ℓ)).toIntAlgHom.toLinearMap) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul o a =>
        simp only [Function.comp_apply, LinearMap.lTensor_tmul, TensorProduct.comm_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, hf]
        rfl
      | add x y hx hy =>
        simp only [Function.comp_apply, map_add] at hx hy ⊢
        rw [hx, hy]
    rw [heq]
    exact (LinearEquiv.injective _).comp ((LinearEquiv.injective _).comp hl)
  have hmem : ∀ x, f x ∈ locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o a =>
      rw [hf]
      have h1 : (a : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) =
          algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) a * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o)) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rfl
      rw [h1]
      refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) (Algebra.subset_adjoin ?_)
      exact ⟨(1 : ℚ) ⊗ₜ[ℤ] o, ⟨o, rfl⟩, rfl⟩
    | add x y hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  let g : O ⊗[ℤ] ℤ_[ℓ] →+* locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range :=
    (f.toRingHom).codRestrict _ hmem
  have hsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ (locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range).toSubring := hy
    rw [locOrder, Algebra.adjoin_eq_ring_closure] at hy'
    have hle : Subring.closure (Set.range (algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O))) ∪
        ((fun b => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) '' ((Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range : Set (ℚ ⊗[ℤ] O)))) ≤ f.toRingHom.range := by
      rw [Subring.closure_le]
      rintro _ (⟨a, rfl⟩ | ⟨_, ⟨o, rfl⟩, rfl⟩)
      · refine ⟨(1 : O) ⊗ₜ a, ?_⟩
        change f _ = _
        rw [hf, Algebra.TensorProduct.algebraMap_apply]
        rfl
      · refine ⟨o ⊗ₜ (1 : ℤ_[ℓ]), ?_⟩
        change f _ = _
        rw [hf]
        simp
    obtain ⟨x, hx⟩ := hle hy'
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨RingEquiv.ofBijective g ⟨fun x y h => hinj (congrArg Subtype.val h), hsurj⟩, fun o => ?_⟩
  change f (o ⊗ₜ 1) = _
  rw [hf]
  simp

end GlobalTheory.LocIso
