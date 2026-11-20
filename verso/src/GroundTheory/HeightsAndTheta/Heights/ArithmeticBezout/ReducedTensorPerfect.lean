import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open TensorProduct

noncomputable section

universe u

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Apply `IsReduced.tensorProduct_of_flat_of_forall_fg` to reduce the goal to its premises. Introduce `B hB`. Establish `: IsReduced B` using `isReduced_of_injective B.val Subtype.val_injective`. Establish `: Algebra.FiniteType k B` using `⟨(Subalgebra.fg_top B).mpr hB⟩`. Establish `: IsNoetherianRing B` using `Algebra.FiniteType.isNoetherianRing k B`.

Establish `: Fintype (minimalPrimes B)` using `(minimalPrimes.finite_of_isNoetherianRing B).fintype`. Establish `hP : ∀ P : minimalPrimes B, P.1.IsPrime` using `fun P => P.2.1.1`. Set `φ : B →ₐ[k] ∀ P : minimalPrimes B, FractionRing (B ⧸ P.1)` to `AlgHom.pi fun P => (IsScalarTower.toAlgHom k (B ⧸ P.1) (FractionRing (B ⧸ P.1))).comp (Ideal.Quotient.mkₐ k P.1)`. Establish `hφ : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `b hb`. Establish `hmem : b ∈ sInf (minimalPrimes B)`. Rewrite using `[Submodule.mem_sInf]`. Introduce `P hPm`. Establish `h1` using `congr_fun hb ⟨P, hPm⟩`.

Establish `h2 : algebraMap (B ⧸ P) (FractionRing (B ⧸ P)) (Ideal.Quotient.mk P b) = 0` using `h1`. Rewrite `h2` using `[IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `h2`. Rewrite `hmem` using `[minimalPrimes, Ideal.sInf_minimalPrimes]`. Establish `: b ∈ nilradical B` using `hmem`.

Rewrite `this` using `[nilradical_eq_zero]`. Conclude with `this`. Establish `hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id C C) φ)` using `Module.Flat.lTensor_preserves_injective_linearMap (φ.toLinearMap) hφ`. Establish `: ∀ P : minimalPrimes B, IsReduced (C ⊗[k] FractionRing (B ⧸ P.1))` using `fun P => h _`. Set `ψ` to `Algebra.TensorProduct.piRight k k C (fun P : minimalPrimes B => FractionRing (B ⧸ P.1))`.

Conclude with `isReduced_of_injective (ψ.toRingEquiv.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id C C) φ).toRingHom) ((AlgEquiv.injective ψ).comp hinj)`.
-/
theorem isReduced_tensorProduct_of_forall_field {k : Type*} [Field k] (C : Type*) [CommRing C]
    [Algebra k C]
    (h : ∀ (E : Type u) [Field E] [Algebra k E] [Algebra.EssFiniteType k E], IsReduced (C ⊗[k] E))
    (A : Type u) [CommRing A] [Algebra k A] [IsReduced A] : IsReduced (C ⊗[k] A) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : Algebra.FiniteType k B := ⟨(Subalgebra.fg_top B).mpr hB⟩
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have : Fintype (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).fintype
  classical
  have hP : ∀ P : minimalPrimes B, P.1.IsPrime := fun P => P.2.1.1
  let φ : B →ₐ[k] ∀ P : minimalPrimes B, FractionRing (B ⧸ P.1) :=
    AlgHom.pi fun P =>
      (IsScalarTower.toAlgHom k (B ⧸ P.1) (FractionRing (B ⧸ P.1))).comp (Ideal.Quotient.mkₐ k P.1)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hmem : b ∈ sInf (minimalPrimes B) := by
      rw [Submodule.mem_sInf]
      intro P hPm
      have h1 := congr_fun hb ⟨P, hPm⟩
      have h2 : algebraMap (B ⧸ P) (FractionRing (B ⧸ P)) (Ideal.Quotient.mk P b) = 0 := h1
      rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h2
      exact h2
    rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hmem
    have : b ∈ nilradical B := hmem
    rw [nilradical_eq_zero] at this
    exact this
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id C C) φ) :=
    Module.Flat.lTensor_preserves_injective_linearMap (φ.toLinearMap) hφ
  have : ∀ P : minimalPrimes B, IsReduced (C ⊗[k] FractionRing (B ⧸ P.1)) := fun P => h _
  let ψ := Algebra.TensorProduct.piRight k k C (fun P : minimalPrimes B => FractionRing (B ⧸ P.1))
  exact isReduced_of_injective (ψ.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id C C) φ).toRingHom)
    ((AlgEquiv.injective ψ).comp hinj)

/- English proof (translation)
Use `isReduced_tensorProduct_of_forall_field E (fun M _ _ _ => ?_) D` and prove the remaining obligations. Establish `: Algebra.FormallyUnramified F E` using `Algebra.FormallyUnramified.of_isSeparable F E`. Establish `: IsReduced (M ⊗[F] E)` using `Algebra.FormallyUnramified.isReduced_of_field M (M ⊗[F] E)`. Conclude with `isReduced_of_injective (Algebra.TensorProduct.comm F E M).toAlgHom (AlgEquiv.injective _)`.
-/
theorem isReduced_tensorProduct_of_isSeparable {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] [Algebra.EssFiniteType F E]
    (D : Type u) [CommRing D] [Algebra F D] [IsReduced D] : IsReduced (E ⊗[F] D) := by
  refine isReduced_tensorProduct_of_forall_field E (fun M _ _ _ => ?_) D
  have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
  have : IsReduced (M ⊗[F] E) := Algebra.FormallyUnramified.isReduced_of_field M (M ⊗[F] E)
  exact isReduced_of_injective (Algebra.TensorProduct.comm F E M).toAlgHom (AlgEquiv.injective _)

/- English proof (translation)
Set `R` to `MvPolynomial σ K`. Establish `: IsReduced (R ⊗[K] L)` using `isReduced_of_injective ((Algebra.TensorProduct.comm K R L).toRingEquiv.trans (MvPolynomial.algebraTensorAlgEquiv K L).toRingEquiv) (RingEquiv.injective _)`. Establish `: IsReduced (FractionRing R ⊗[R] (R ⊗[K] L))`. Set `: Algebra (R ⊗[K] L) (FractionRing R ⊗[R] (R ⊗[K] L))` to `Algebra.TensorProduct.rightAlgebra`. Conclude with `isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (R ⊗[K] L) (nonZeroDivisors R)) (FractionRing R ⊗[R] (R ⊗[K] L)) inferInstance`.

Conclude with `isReduced_of_injective (Algebra.TensorProduct.cancelBaseChange K R R (FractionRing R) L).symm.toAlgHom (AlgEquiv.injective _)`.
-/
theorem isReduced_fractionRing_mvPolynomial_tensorProduct (K : Type u) [Field K] (σ : Type u)
    (L : Type u) [Field L] [Algebra K L] :
    IsReduced (FractionRing (MvPolynomial σ K) ⊗[K] L) := by
  let R := MvPolynomial σ K
  have : IsReduced (R ⊗[K] L) :=
    isReduced_of_injective
      ((Algebra.TensorProduct.comm K R L).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv K L).toRingEquiv)
      (RingEquiv.injective _)
  have : IsReduced (FractionRing R ⊗[R] (R ⊗[K] L)) := by
    let : Algebra (R ⊗[K] L) (FractionRing R ⊗[R] (R ⊗[K] L)) := Algebra.TensorProduct.rightAlgebra
    exact isReduced_localizationPreserves
      (Algebra.algebraMapSubmonoid (R ⊗[K] L) (nonZeroDivisors R))
      (FractionRing R ⊗[R] (R ⊗[K] L)) inferInstance
  exact isReduced_of_injective
    (Algebra.TensorProduct.cancelBaseChange K R R (FractionRing R) L).symm.toAlgHom
    (AlgEquiv.injective _)

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Take `⟨s, hs, H⟩` from `exists_isTranscendenceBasis_and_isSeparable_of_perfectField K E`. Set `F` to `IntermediateField.adjoin K (s : Set E)`. Establish `: Algebra.EssFiniteType F E` using `Algebra.EssFiniteType.of_comp K F E`. Set `e : FractionRing (MvPolynomial s K) ≃ₐ[K] F` to `hs.1.aevalEquivField.trans (IntermediateField.equivOfEq (by simp [F]))`. Establish `: IsReduced (FractionRing (MvPolynomial s K) ⊗[K] L)` using `isReduced_fractionRing_mvPolynomial_tensorProduct K s L`.

Establish `: IsReduced (F ⊗[K] L)` using `isReduced_of_injective (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).toAlgHom (AlgEquiv.injective _)`. Establish `hD` using `isReduced_tensorProduct_of_isSeparable (F := F) (E := E) (F ⊗[K] L)`. Conclude with `@isReduced_of_injective _ _ _ _ _ _ _ ((Algebra.TensorProduct.comm K L E).toRingEquiv.trans (Algebra.TensorProduct.cancelBaseChange K F F E L).symm.toRingEquiv) (RingEquiv.injective _) hD`.
-/
theorem isReduced_tensorProduct_field_of_perfectField (K : Type u) [Field K] [PerfectField K]
    (L : Type u) [Field L] [Algebra K L] (E : Type u) [Field E] [Algebra K E]
    [Algebra.EssFiniteType K E] : IsReduced (L ⊗[K] E) := by
  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K E
  let F := IntermediateField.adjoin K (s : Set E)
  have : Algebra.EssFiniteType F E := Algebra.EssFiniteType.of_comp K F E
  let e : FractionRing (MvPolynomial s K) ≃ₐ[K] F :=
    hs.1.aevalEquivField.trans (IntermediateField.equivOfEq (by simp [F]))
  have : IsReduced (FractionRing (MvPolynomial s K) ⊗[K] L) :=
    isReduced_fractionRing_mvPolynomial_tensorProduct K s L
  have : IsReduced (F ⊗[K] L) :=
    isReduced_of_injective (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).toAlgHom
      (AlgEquiv.injective _)
  have hD := isReduced_tensorProduct_of_isSeparable (F := F) (E := E) (F ⊗[K] L)
  exact @isReduced_of_injective _ _ _ _ _ _ _
    ((Algebra.TensorProduct.comm K L E).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange K F F E L).symm.toRingEquiv)
    (RingEquiv.injective _) hD

/- English proof (translation)
The claim follows from `isReduced_tensorProduct_of_forall_field L (fun E _ _ _ => isReduced_tensorProduct_field_of_perfectField K L E) A`.
-/
theorem isReduced_tensorProduct_of_perfectField (K : Type u) [Field K] [PerfectField K]
    (L : Type u) [Field L] [Algebra K L] (A : Type u) [CommRing A] [Algebra K A] [IsReduced A] :
    IsReduced (L ⊗[K] A) :=
  isReduced_tensorProduct_of_forall_field L
    (fun E _ _ _ => isReduced_tensorProduct_field_of_perfectField K L E) A

end

end GroundTheory.Heights₂.Heights
