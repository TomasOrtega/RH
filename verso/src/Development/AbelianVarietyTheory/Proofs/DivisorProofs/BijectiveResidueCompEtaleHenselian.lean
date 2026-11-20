import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RangeLeRangeOfIsUnramifiedAt

open IsLocalRing

namespace GlobalTheory.EtaleHensel

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/- English proof (translation)
Take `⟨t, ht, ht1⟩` from `(Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := A)).mp inferInstance`. Set `ψ : TensorProduct R A A →ₐ[R] B` to `Algebra.TensorProduct.productMap φ₁ φ₂`. Set `ρ : B →ₐ[R] ResidueField B` to `IsScalarTower.toAlgHom R B (ResidueField B)`. Establish `hρ : ∀ b, ρ b = residue B b` using `fun _ => rfl`. Establish `key : ρ.comp ψ = (ρ.comp φ₁).comp (Algebra.TensorProduct.lmul' R)`.

Apply `Algebra.TensorProduct.ext'` to reduce the goal to its premises. Introduce `a b`. Simplify using `only [AlgHom.comp_apply, ψ, Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_mul, hρ, h b]`. Establish `hres : residue B (ψ t) = 1`. Use `congrArg (fun f : TensorProduct R A A →ₐ[R] ResidueField B => f t) key` as an intermediate fact.

Simplify `this` using `only [AlgHom.comp_apply, ht1, map_one, hρ]`. Establish `hu : IsUnit (ψ t)`. Assume the negation of the conclusion as `hn`. Establish `h0 : residue B (ψ t) = 0` using `(residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hn)`. Conclude with `one_ne_zero (hres.symm.trans h0)`.

Use extensionality with `a`. Establish `hz` using `congrArg ψ (ht a)`. Simplify using `only [map_mul, map_sub, map_zero, ψ, Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul, mul_one] at hz`. Conclude with `(sub_eq_zero.mp (hu.mul_left_eq_zero.mp hz)).symm`.
-/
theorem algHom_eq_of_residue_eq [Algebra.Etale R A] [IsLocalRing B] {φ₁ φ₂ : A →ₐ[R] B}
    (h : ∀ a, residue B (φ₁ a) = residue B (φ₂ a)) : φ₁ = φ₂ := by

  obtain ⟨t, ht, ht1⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := A)).mp inferInstance
  let ψ : TensorProduct R A A →ₐ[R] B := Algebra.TensorProduct.productMap φ₁ φ₂
  let ρ : B →ₐ[R] ResidueField B := IsScalarTower.toAlgHom R B (ResidueField B)
  have hρ : ∀ b, ρ b = residue B b := fun _ => rfl
  have key : ρ.comp ψ = (ρ.comp φ₁).comp (Algebra.TensorProduct.lmul' R) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [AlgHom.comp_apply, ψ, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, map_mul, hρ, h b]
  have hres : residue B (ψ t) = 1 := by
    have := congrArg (fun f : TensorProduct R A A →ₐ[R] ResidueField B => f t) key
    simpa only [AlgHom.comp_apply, ht1, map_one, hρ] using this
  have hu : IsUnit (ψ t) := by
    by_contra hn
    have h0 : residue B (ψ t) = 0 := (residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hn)
    exact one_ne_zero (hres.symm.trans h0)
  ext a
  have hz := congrArg ψ (ht a)
  simp only [map_mul, map_sub, map_zero, ψ, Algebra.TensorProduct.productMap_apply_tmul,
    map_one, one_mul, mul_one] at hz
  exact (sub_eq_zero.mp (hu.mul_left_eq_zero.mp hz)).symm

/- English proof (translation)
Introduce `R A B _ _ _ _ _ _ _`. Use `⟨fun φ₁ φ₂ he => algHom_eq_of_residue_eq fun a => ?_, fun φ => ?_⟩` and prove the remaining obligations. Conclude with `DFunLike.congr_fun he a`. Take `⟨ψ, hψ⟩` from `GlobalTheory.exists_algHom_lift_of_smooth (maximalIdeal B) (IsScalarTower.toAlgHom R B (ResidueField B)) residue_surjective (fun b => (residue_eq_zero_iff b).symm) φ`. Conclude with `⟨ψ, hψ⟩`.
-/
theorem bijective_residue_comp : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.Etale R A] [HenselianLocalRing B],
    Function.Bijective
      (fun φ : A →ₐ[R] B => (IsScalarTower.toAlgHom R B (ResidueField B)).comp φ) := by
  intro R A B _ _ _ _ _ _ _
  refine ⟨fun φ₁ φ₂ he => algHom_eq_of_residue_eq fun a => ?_, fun φ => ?_⟩
  · exact DFunLike.congr_fun he a
  · obtain ⟨ψ, hψ⟩ := GlobalTheory.exists_algHom_lift_of_smooth (maximalIdeal B)
      (IsScalarTower.toAlgHom R B (ResidueField B)) residue_surjective
      (fun b => (residue_eq_zero_iff b).symm) φ
    exact ⟨ψ, hψ⟩

end GlobalTheory.EtaleHensel
