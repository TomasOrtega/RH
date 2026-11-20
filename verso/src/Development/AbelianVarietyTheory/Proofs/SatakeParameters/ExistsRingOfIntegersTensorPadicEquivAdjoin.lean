import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CenOrderIso

def toLocal (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] :
    𝓞 F ⊗[ℤ] ℤ_[ℓ] →+* ℚ_[ℓ] ⊗[ℚ] F :=
  (Algebra.TensorProduct.equivOfCompatibleSMul ℤ ℚ ℚ_[ℓ] ℚ_[ℓ] F).symm.toRingEquiv.toRingHom.comp
    ((Algebra.TensorProduct.comm ℤ F ℚ_[ℓ]).toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.map (algebraMap (𝓞 F) F).toIntAlgHom
        (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom).toRingHom)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toLocal_tmul (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (c : 𝓞 F) (a : ℤ_[ℓ]) :
    toLocal F ℓ (c ⊗ₜ[ℤ] a) = (a : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) := rfl

/- English proof (translation)
Establish `h1 : Function.Injective ((algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom.toLinearMap.lTensor (𝓞 F))` using `Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ])`. Establish `h2 : Function.Injective ((algebraMap (𝓞 F) F).toIntAlgHom.toLinearMap.rTensor ℚ_[ℓ])` using `Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective (𝓞 F) F)`. Establish `hmap : Function.Injective (Algebra.TensorProduct.map (algebraMap (𝓞 F) F).toIntAlgHom (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom)`. Establish `: ⇑(Algebra.TensorProduct.map (algebraMap (𝓞 F) F).toIntAlgHom (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom) = ((algebraMap (𝓞 F) F).toIntAlgHom.toLinearMap.rTensor ℚ_[ℓ]) ∘ ((algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom.toLinearMap.lTensor (𝓞 F))`. Use function extensionality and compare the values at `w`.

Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => rfl`. Consider the case `add a b ha hb => simp only [map_add, Function.comp_apply] at ha hb ⊢`. Rewrite using `[ha, hb]`.

Rewrite using `[this]`. Conclude with `h2.comp h1`. Introduce `x y hxy`. Apply `hmap` to reduce the goal to its premises. Apply `(Algebra.TensorProduct.comm ℤ F ℚ_[ℓ]).injective` to reduce the goal to its premises.

Conclude with `(Algebra.TensorProduct.equivOfCompatibleSMul ℤ ℚ ℚ_[ℓ] ℚ_[ℓ] F).symm.injective hxy`.
-/
theorem toLocal_injective (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Injective (toLocal F ℓ) := by
  have h1 : Function.Injective
      ((algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom.toLinearMap.lTensor (𝓞 F)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ])
  have h2 : Function.Injective
      ((algebraMap (𝓞 F) F).toIntAlgHom.toLinearMap.rTensor ℚ_[ℓ]) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective (𝓞 F) F)
  have hmap : Function.Injective (Algebra.TensorProduct.map (algebraMap (𝓞 F) F).toIntAlgHom
      (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom) := by
    have : ⇑(Algebra.TensorProduct.map (algebraMap (𝓞 F) F).toIntAlgHom
        (algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom) =
        ((algebraMap (𝓞 F) F).toIntAlgHom.toLinearMap.rTensor ℚ_[ℓ]) ∘
        ((algebraMap ℤ_[ℓ] ℚ_[ℓ]).toIntAlgHom.toLinearMap.lTensor (𝓞 F)) := by
      funext w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => rfl
      | add a b ha hb => simp only [map_add, Function.comp_apply] at ha hb ⊢; rw [ha, hb]
    rw [this]; exact h2.comp h1
  intro x y hxy
  apply hmap
  apply (Algebra.TensorProduct.comm ℤ F ℚ_[ℓ]).injective
  exact (Algebra.TensorProduct.equivOfCompatibleSMul ℤ ℚ ℚ_[ℓ] ℚ_[ℓ] F).symm.injective hxy

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `tmul c a`. Rewrite using `[toLocal_tmul]`.

Establish `hc : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) ∈ cenOrder ℓ F` using `Algebra.subset_adjoin ⟨c, rfl⟩`. Establish `: (a : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) = a • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F))`. Rewrite using `[TensorProduct.smul_tmul']`. Use `congr 1`. Use `show (a : ℚ_[ℓ]) = a • (1 : ℚ_[ℓ])`.

Rewrite using `[Algebra.smul_def, mul_one]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Subalgebra.smul_mem _ hc a`. Consider the case `add x y hx hy => rw [map_add]`.

Conclude with `add_mem hx hy`.
-/
theorem toLocal_mem (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] (x : 𝓞 F ⊗[ℤ] ℤ_[ℓ]) :
    toLocal F ℓ x ∈ cenOrder ℓ F := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul c a =>
    rw [toLocal_tmul]
    have hc : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) ∈ cenOrder ℓ F :=
      Algebra.subset_adjoin ⟨c, rfl⟩
    have : (a : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) = a • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F)) := by
      rw [TensorProduct.smul_tmul']
      congr 1
      show (a : ℚ_[ℓ]) = a • (1 : ℚ_[ℓ])
      rw [Algebra.smul_def, mul_one]; rfl
    rw [this]
    exact Subalgebra.smul_mem _ hc a
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/- English proof (translation)
Set `S : Subalgebra ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F)` to `{ (toLocal F ℓ).range with algebraMap_mem' := fun r => ⟨(1 : 𝓞 F) ⊗ₜ[ℤ] r, by`. Rewrite using `[toLocal_tmul]`. Use the proof step `rfl⟩ }`. Establish `hle : cenOrder ℓ F ≤ S`. Apply `Algebra.adjoin_le` to reduce the goal to its premises.

Introduce and unpack `_ ⟨c, rfl⟩`. Conclude with `⟨c ⊗ₜ[ℤ] (1 : ℤ_[ℓ]), by rw [toLocal_tmul]; simp⟩`. Introduce `y hy`. Conclude with `hle hy`.
-/
theorem cenOrder_le_range (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∀ y ∈ cenOrder ℓ F, ∃ x, toLocal F ℓ x = y := by
  let S : Subalgebra ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F) :=
    { (toLocal F ℓ).range with
      algebraMap_mem' := fun r => ⟨(1 : 𝓞 F) ⊗ₜ[ℤ] r, by
        rw [toLocal_tmul]; rfl⟩ }
  have hle : cenOrder ℓ F ≤ S := by
    apply Algebra.adjoin_le
    rintro _ ⟨c, rfl⟩
    exact ⟨c ⊗ₜ[ℤ] (1 : ℤ_[ℓ]), by rw [toLocal_tmul]; simp⟩
  intro y hy
  exact hle hy

/- English proof (translation)
Introduce `F _ _ ℓ _`. Set `g : 𝓞 F ⊗[ℤ] ℤ_[ℓ] →+* cenOrder ℓ F` to `(toLocal F ℓ).codRestrict (cenOrder ℓ F) (toLocal_mem F ℓ)`. Establish `hbij : Function.Bijective g`. Use `⟨fun x y h => toLocal_injective F ℓ (congrArg Subtype.val h), fun y => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `cenOrder_le_range F ℓ y y.2`.

Conclude with `⟨x, Subtype.ext hx⟩`. Use `⟨RingEquiv.ofBijective g hbij, fun c => ?_⟩` and prove the remaining obligations. Use `show toLocal F ℓ (c ⊗ₜ[ℤ] 1) = _`. Rewrite using `[toLocal_tmul]`. Simplify using the standard rewrite rules.
-/
theorem cenOrder_equiv : ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime],
    ∃ κ : 𝓞 F ⊗[ℤ] ℤ_[ℓ] ≃+* cenOrder ℓ F,
      ∀ c : 𝓞 F, (κ (c ⊗ₜ[ℤ] 1) : ℚ_[ℓ] ⊗[ℚ] F) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (c : F) := by
  intro F _ _ ℓ _
  let g : 𝓞 F ⊗[ℤ] ℤ_[ℓ] →+* cenOrder ℓ F := (toLocal F ℓ).codRestrict (cenOrder ℓ F) (toLocal_mem F ℓ)
  have hbij : Function.Bijective g := by
    refine ⟨fun x y h => toLocal_injective F ℓ (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := cenOrder_le_range F ℓ y y.2
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨RingEquiv.ofBijective g hbij, fun c => ?_⟩
  show toLocal F ℓ (c ⊗ₜ[ℤ] 1) = _
  rw [toLocal_tmul]; simp

end GlobalTheory.CenOrderIso
