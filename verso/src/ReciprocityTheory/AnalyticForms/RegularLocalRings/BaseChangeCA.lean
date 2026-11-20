import Mathlib

namespace ReciprocityTheory.AnForm.R.BaseChangeC

open MvPolynomial TensorProduct

section FracTensor

variable (ι : Type) (F : Type) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial ι ℚ) F]
  [IsScalarTower ℚ (MvPolynomial ι ℚ) F] [IsFractionRing (MvPolynomial ι ℚ) F]
  (C : Type) [Field C] [Algebra ℚ C]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨1, one_mem _, 0, by simp⟩`. Consider the case `tmul a c`. Take `⟨⟨x, s⟩, hs⟩` from `IsLocalization.surj (nonZeroDivisors (MvPolynomial ι ℚ)) a`. Use `⟨(s : MvPolynomial ι ℚ), s.2, x ⊗ₜ[ℚ] c, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.map_tmul, mul_comm, hs]`. Both sides reduce to the same expression. Consider the case `add z₁ z₂ h₁ h₂`. Take `⟨s₁, hs₁, w₁, e₁⟩` from `h₁`. Take `⟨s₂, hs₂, w₂, e₂⟩` from `h₂`.

Use `⟨s₁ * s₂, mul_mem hs₁ hs₂, (s₂ ⊗ₜ[ℚ] (1 : C)) * w₁ + (s₁ ⊗ₜ[ℚ] (1 : C)) * w₂, ?_⟩` and prove the remaining obligations. Establish `hΦ : ∀ t : MvPolynomial ι ℚ, Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F) (AlgHom.id ℚ C) (t ⊗ₜ[ℚ] (1 : C)) = algebraMap (MvPolynomial ι ℚ) F t ⊗ₜ[ℚ] (1 : C)` using `fun t => by`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Both sides reduce to the same expression. Establish `hsplit : (algebraMap (MvPolynomial ι ℚ) F s₁ * algebraMap (MvPolynomial ι ℚ) F s₂) ⊗ₜ[ℚ] (1 : C) = (algebraMap (MvPolynomial ι ℚ) F s₁ ⊗ₜ[ℚ] (1 : C)) * (algebraMap (MvPolynomial ι ℚ) F s₂ ⊗ₜ[ℚ] (1 : C))`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one]`. Simplify using `only [map_add, map_mul, hΦ]`. Rewrite using `[← e₁, ← e₂, hsplit]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fracTensor_exists_den (z : F ⊗[ℚ] C) :
    ∃ s ∈ nonZeroDivisors (MvPolynomial ι ℚ), ∃ w : MvPolynomial ι ℚ ⊗[ℚ] C,
      (algebraMap (MvPolynomial ι ℚ) F s ⊗ₜ[ℚ] (1 : C)) * z =
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F)
          (AlgHom.id ℚ C) w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, 0, by simp⟩
  | tmul a c =>
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (MvPolynomial ι ℚ)) a
    refine ⟨(s : MvPolynomial ι ℚ), s.2, x ⊗ₜ[ℚ] c, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.map_tmul, mul_comm, hs]
    rfl
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨s₁, hs₁, w₁, e₁⟩ := h₁
    obtain ⟨s₂, hs₂, w₂, e₂⟩ := h₂
    refine ⟨s₁ * s₂, mul_mem hs₁ hs₂,
      (s₂ ⊗ₜ[ℚ] (1 : C)) * w₁ + (s₁ ⊗ₜ[ℚ] (1 : C)) * w₂, ?_⟩
    have hΦ : ∀ t : MvPolynomial ι ℚ,
        Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F) (AlgHom.id ℚ C)
          (t ⊗ₜ[ℚ] (1 : C)) = algebraMap (MvPolynomial ι ℚ) F t ⊗ₜ[ℚ] (1 : C) := fun t => by
      rw [Algebra.TensorProduct.map_tmul]; rfl
    have hsplit : (algebraMap (MvPolynomial ι ℚ) F s₁ * algebraMap (MvPolynomial ι ℚ) F s₂) ⊗ₜ[ℚ] (1 : C) =
        (algebraMap (MvPolynomial ι ℚ) F s₁ ⊗ₜ[ℚ] (1 : C)) *
          (algebraMap (MvPolynomial ι ℚ) F s₂ ⊗ₜ[ℚ] (1 : C)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp only [map_add, map_mul, hΦ]
    rw [← e₁, ← e₂, hsplit]
    ring

include ι in
/- English proof (translation)
Establish `h1 : Function.Injective (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F)` using `IsFractionRing.injective (MvPolynomial ι ℚ) F`. Establish `hinj : Function.Injective (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F) (AlgHom.id ℚ C))` using `Module.Flat.rTensor_preserves_injective_linearMap (M := C) (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F).toLinearMap h1`. Set `e : MvPolynomial ι ℚ ⊗[ℚ] C ≃+* MvPolynomial ι C` to `(Algebra.TensorProduct.comm ℚ (MvPolynomial ι ℚ) C).toRingEquiv.trans (MvPolynomial.algebraTensorAlgEquiv (σ := ι) ℚ C).toRingEquiv`. Use `haveI hD : IsDomain (MvPolynomial ι ℚ ⊗[ℚ] C) := Function.Injective.isDomain e e.injective`. Use `haveI : Nontrivial (F ⊗[ℚ] C) := hinj.nontrivial`.

Establish `hu : ∀ s ∈ nonZeroDivisors (MvPolynomial ι ℚ), IsUnit (algebraMap (MvPolynomial ι ℚ) F s ⊗ₜ[ℚ] (1 : C))`. Introduce `s hs`. Establish `h0 : algebraMap (MvPolynomial ι ℚ) F s ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs`. Conclude with `(isUnit_iff_ne_zero.mpr h0).map (Algebra.TensorProduct.includeLeftRingHom (R := ℚ) (A := F) (B := C))`. Use `haveI nzd : NoZeroDivisors (F ⊗[ℚ] C) := by`.

Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Take `⟨s₁, hs₁, w₁, e₁⟩` from `fracTensor_exists_den ι F C a`. Take `⟨s₂, hs₂, w₂, e₂⟩` from `fracTensor_exists_den ι F C b`. Establish `hw : Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F) (AlgHom.id ℚ C) (w₁ * w₂) = 0`.

Rewrite using `[map_mul, ← e₁, ← e₂]`. Combine the equalities or inequalities in the displayed calculation. Establish `hw0 : w₁ * w₂ = 0` using `hinj (by rw [hw, map_zero])`. Break down `mul_eq_zero.mp hw0 with h | h` into its components or cases. Use `left`.

Establish `h' : (algebraMap (MvPolynomial ι ℚ) F s₁ ⊗ₜ[ℚ] (1 : C)) * a = 0`. Rewrite using `[e₁, h, map_zero]`. Conclude with `((hu s₁ hs₁).mul_right_eq_zero).mp h'`. Use `right`. Establish `h' : (algebraMap (MvPolynomial ι ℚ) F s₂ ⊗ₜ[ℚ] (1 : C)) * b = 0`.

Rewrite using `[e₂, h, map_zero]`. Conclude with `((hu s₂ hs₂).mul_right_eq_zero).mp h'`. Conclude with `NoZeroDivisors.to_isDomain _`.
-/
theorem isDomain_tensor_of_isFractionRing : IsDomain (F ⊗[ℚ] C) := by
  have h1 : Function.Injective (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F) :=
    IsFractionRing.injective (MvPolynomial ι ℚ) F
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F) (AlgHom.id ℚ C)) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := C)
      (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F).toLinearMap h1
  let e : MvPolynomial ι ℚ ⊗[ℚ] C ≃+* MvPolynomial ι C :=
    (Algebra.TensorProduct.comm ℚ (MvPolynomial ι ℚ) C).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv (σ := ι) ℚ C).toRingEquiv
  haveI hD : IsDomain (MvPolynomial ι ℚ ⊗[ℚ] C) := Function.Injective.isDomain e e.injective
  haveI : Nontrivial (F ⊗[ℚ] C) := hinj.nontrivial
  have hu : ∀ s ∈ nonZeroDivisors (MvPolynomial ι ℚ),
      IsUnit (algebraMap (MvPolynomial ι ℚ) F s ⊗ₜ[ℚ] (1 : C)) := by
    intro s hs
    have h0 : algebraMap (MvPolynomial ι ℚ) F s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    exact (isUnit_iff_ne_zero.mpr h0).map
      (Algebra.TensorProduct.includeLeftRingHom (R := ℚ) (A := F) (B := C))
  haveI nzd : NoZeroDivisors (F ⊗[ℚ] C) := by
    constructor
    intro a b hab
    obtain ⟨s₁, hs₁, w₁, e₁⟩ := fracTensor_exists_den ι F C a
    obtain ⟨s₂, hs₂, w₂, e₂⟩ := fracTensor_exists_den ι F C b
    have hw : Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℚ (MvPolynomial ι ℚ) F)
        (AlgHom.id ℚ C) (w₁ * w₂) = 0 := by
      rw [map_mul, ← e₁, ← e₂]
      calc _ = (algebraMap (MvPolynomial ι ℚ) F s₁ ⊗ₜ[ℚ] (1 : C)) *
            (algebraMap (MvPolynomial ι ℚ) F s₂ ⊗ₜ[ℚ] (1 : C)) * (a * b) := by ring
        _ = 0 := by rw [hab, mul_zero]
    have hw0 : w₁ * w₂ = 0 := hinj (by rw [hw, map_zero])
    rcases mul_eq_zero.mp hw0 with h | h
    · left
      have h' : (algebraMap (MvPolynomial ι ℚ) F s₁ ⊗ₜ[ℚ] (1 : C)) * a = 0 := by
        rw [e₁, h, map_zero]
      exact ((hu s₁ hs₁).mul_right_eq_zero).mp h'
    · right
      have h' : (algebraMap (MvPolynomial ι ℚ) F s₂ ⊗ₜ[ℚ] (1 : C)) * b = 0 := by
        rw [e₂, h, map_zero]
      exact ((hu s₂ hs₂).mul_right_eq_zero).mp h'
  exact NoZeroDivisors.to_isDomain _

end FracTensor

section Red

attribute [-instance] DivisionRing.toRatAlgebra

/- English proof (translation)
Set `M` to `FractionRing D`. Establish `hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id F K) (IsScalarTower.toAlgHom F D M))` using `Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)`. Establish `: IsReduced (K ⊗[F] M)`. Use `Algebra.FormallyUnramified.isReduced_of_field M (M ⊗[F] K)` as an intermediate fact. Conclude with `isReduced_of_injective (Algebra.TensorProduct.comm F K M).toRingEquiv.toRingHom (Algebra.TensorProduct.comm F K M).injective`.

Conclude with `isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id F K) (IsScalarTower.toAlgHom F D M)).toRingHom hinj`.
-/
theorem isReduced_tensor_domain (F K D : Type) [Field F] [Field K] [Algebra F K]
    [Algebra.FormallyUnramified F K] [Algebra.EssFiniteType F K] [CommRing D] [IsDomain D]
    [Algebra F D] : IsReduced (K ⊗[F] D) := by
  let M := FractionRing D
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id F K)
      (IsScalarTower.toAlgHom F D M)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  have : IsReduced (K ⊗[F] M) := by
    have := Algebra.FormallyUnramified.isReduced_of_field M (M ⊗[F] K)
    exact isReduced_of_injective (Algebra.TensorProduct.comm F K M).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm F K M).injective
  exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id F K)
      (IsScalarTower.toAlgHom F D M)).toRingHom hinj

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_isTranscendenceBasis ℚ K`. Use `set F0 := IntermediateField.adjoin ℚ (Set.range ((↑) : s → K))`. Establish `: Algebra.IsAlgebraic F0 K` using `hs.isAlgebraic_field`. Establish `: PerfectField F0` using `@PerfectField.ofCharZero F0 _ (charZero_of_injective_algebraMap (algebraMap ℚ F0).injective)`. Establish `: Algebra.IsSeparable F0 K` using `Algebra.IsAlgebraic.isSeparable_of_perfectField`.

Establish `: Algebra.FormallyUnramified F0 K` using `Algebra.FormallyUnramified.of_isSeparable F0 K`. Establish `: Algebra.EssFiniteType F0 K` using `Algebra.EssFiniteType.of_comp ℚ F0 K`. Set `e` to `hs.1.aevalEquivField`. Use `letI : Algebra (MvPolynomial s ℚ) F0 := (e.toRingEquiv.toRingHom.comp (algebraMap (MvPolynomial s ℚ) (FractionRing (MvPolynomial s ℚ)))).toAlgebra`. Use `IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := MvPolynomial s ℚ) (A := F0) (Subsingleton.elim _ _)` as an intermediate fact.

Set `e' : FractionRing (MvPolynomial s ℚ) ≃ₐ[MvPolynomial s ℚ] F0` to `{ e.toRingEquiv with commutes' := fun _ => rfl }`. Establish `: IsFractionRing (MvPolynomial s ℚ) F0` using `IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (MvPolynomial s ℚ)) e'`. Establish `: IsDomain (F0 ⊗[ℚ] C)` using `isDomain_tensor_of_isFractionRing s F0 C`. Establish `: IsReduced (K ⊗[F0] (F0 ⊗[ℚ] C))` using `isReduced_tensor_domain F0 K (F0 ⊗[ℚ] C)`. Conclude with `isReduced_of_injective (Algebra.TensorProduct.cancelBaseChange ℚ F0 K K C).symm.toRingEquiv.toRingHom (Algebra.TensorProduct.cancelBaseChange ℚ F0 K K C).symm.injective`.
-/
theorem isReduced_tensor_of_essFiniteType (K : Type) [Field K] [Algebra ℚ K]
    [Algebra.EssFiniteType ℚ K] (C : Type) [Field C] [Algebra ℚ C] : IsReduced (K ⊗[ℚ] C) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ K
  set F0 := IntermediateField.adjoin ℚ (Set.range ((↑) : s → K))
  have : Algebra.IsAlgebraic F0 K := hs.isAlgebraic_field
  have : PerfectField F0 :=
    @PerfectField.ofCharZero F0 _ (charZero_of_injective_algebraMap (algebraMap ℚ F0).injective)
  have : Algebra.IsSeparable F0 K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Algebra.FormallyUnramified F0 K := Algebra.FormallyUnramified.of_isSeparable F0 K
  have : Algebra.EssFiniteType F0 K := Algebra.EssFiniteType.of_comp ℚ F0 K
  let e := hs.1.aevalEquivField
  letI : Algebra (MvPolynomial s ℚ) F0 :=
    (e.toRingEquiv.toRingHom.comp (algebraMap (MvPolynomial s ℚ) (FractionRing (MvPolynomial s ℚ)))).toAlgebra
  have := IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := MvPolynomial s ℚ) (A := F0)
    (Subsingleton.elim _ _)
  let e' : FractionRing (MvPolynomial s ℚ) ≃ₐ[MvPolynomial s ℚ] F0 :=
    { e.toRingEquiv with commutes' := fun _ => rfl }
  have : IsFractionRing (MvPolynomial s ℚ) F0 :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (MvPolynomial s ℚ)) e'
  have : IsDomain (F0 ⊗[ℚ] C) := isDomain_tensor_of_isFractionRing s F0 C
  have : IsReduced (K ⊗[F0] (F0 ⊗[ℚ] C)) := isReduced_tensor_domain F0 K (F0 ⊗[ℚ] C)
  exact isReduced_of_injective
    (Algebra.TensorProduct.cancelBaseChange ℚ F0 K K C).symm.toRingEquiv.toRingHom
    (Algebra.TensorProduct.cancelBaseChange ℚ F0 K K C).symm.injective

end Red

end ReciprocityTheory.AnForm.R.BaseChangeC
