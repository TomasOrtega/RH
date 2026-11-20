import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPrimeComplexRadical
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial TensorProduct

noncomputable section

/- English proof (translation)
Establish `: IsReduced (FractionRing D ⊗[E] L)` using `Algebra.FormallyUnramified.isReduced_of_field (FractionRing D) (FractionRing D ⊗[E] L)`. Establish `: IsReduced (L ⊗[E] FractionRing D)` using `isReduced_of_injective (Algebra.TensorProduct.comm E L (FractionRing D)) (AlgEquiv.injective _)`. Conclude with `isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id E L) (IsScalarTower.toAlgHom E D (FractionRing D))) (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective D _))`.
-/
theorem isReduced_tensor_domain_of_formallyEtale (E L D : Type*) [Field E] [Field L] [Algebra E L]
    [Algebra.FormallyEtale E L] [Algebra.EssFiniteType E L] [CommRing D] [IsDomain D]
    [Algebra E D] : IsReduced (L ⊗[E] D) := by
  have : IsReduced (FractionRing D ⊗[E] L) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing D) (FractionRing D ⊗[E] L)
  have : IsReduced (L ⊗[E] FractionRing D) :=
    isReduced_of_injective (Algebra.TensorProduct.comm E L (FractionRing D))
      (AlgEquiv.injective _)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id E L) (IsScalarTower.toAlgHom E D (FractionRing D)))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective D _))

open scoped IntermediateField.algebraAdjoinAdjoin in

/- English proof (translation)
Take `⟨s, hs, hsep⟩` from `exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L`. Set `R` to `Algebra.adjoin K (s : Set L)`. Set `E` to `IntermediateField.adjoin K (s : Set L)`. Establish `eR : R ≃ₐ[K] MvPolynomial s K` using `(Subalgebra.equivOfEq R (Algebra.adjoin K (Set.range ((↑) : s → L))) (by simp [R])).trans hs.1.aevalEquiv.symm`. Establish `hRF : IsDomain (R ⊗[K] F)` using `((Algebra.TensorProduct.comm K R F).toRingEquiv.trans ((Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[K] F) eR).toRingEquiv.trans (MvPolynomial.algebraTensorAlgEquiv (σ := s) K F).toRingEquiv)).toMulEquiv.isDomain`.

Establish `hT : IsDomain (E ⊗[R] (R ⊗[K] F))`. Use `letI : Algebra (R ⊗[K] F) (E ⊗[R] (R ⊗[K] F)) := Algebra.TensorProduct.rightAlgebra`. Use `IsLocalization.tensorRight (R := R) (S := R ⊗[K] F) (A := E) (nonZeroDivisors R)` as an intermediate fact. Use `IsLocalization.isDomain_of_le_nonZeroDivisors (R := R ⊗[K] F) (M := Algebra.algebraMapSubmonoid (R ⊗[K] F) (nonZeroDivisors R)) (E ⊗[R] (R ⊗[K] F)) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨r, hr, rfl⟩`.

Use `mem_nonZeroDivisors_of_ne_zero ?_` and prove the remaining obligations. Introduce `h0`. Establish `hinj : Function.Injective (algebraMap R (R ⊗[K] F))` using `Algebra.TensorProduct.includeLeft_injective (S := R) (RingHom.injective (algebraMap K F))`. Conclude with `nonZeroDivisors.ne_zero hr (hinj (by simpa using h0))`. Establish `: IsDomain (E ⊗[K] F)` using `(Algebra.TensorProduct.cancelBaseChange K R R E F).symm.toMulEquiv.isDomain`.

Establish `: Algebra.FormallyEtale E L` using `Algebra.FormallyEtale.of_isSeparable E L`. Establish `: Algebra.EssFiniteType E L` using `Algebra.EssFiniteType.of_comp K E L`. Use `isReduced_tensor_domain_of_formallyEtale E L (E ⊗[K] F)` as an intermediate fact. Conclude with `isReduced_of_injective (Algebra.TensorProduct.cancelBaseChange K E E L F).symm (AlgEquiv.injective _)`.
-/
theorem isReduced_tensor_field_of_perfectField (K L F : Type*) [Field K] [PerfectField K]
    [Field L] [Algebra K L] [Algebra.EssFiniteType K L] [Field F] [Algebra K F] :
    IsReduced (L ⊗[K] F) := by
  classical
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  let R := Algebra.adjoin K (s : Set L)
  let E := IntermediateField.adjoin K (s : Set L)

  have eR : R ≃ₐ[K] MvPolynomial s K :=
    (Subalgebra.equivOfEq R (Algebra.adjoin K (Set.range ((↑) : s → L))) (by simp [R])).trans hs.1.aevalEquiv.symm
  have hRF : IsDomain (R ⊗[K] F) :=
    ((Algebra.TensorProduct.comm K R F).toRingEquiv.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[K] F) eR).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv (σ := s) K F).toRingEquiv)).toMulEquiv.isDomain

  have hT : IsDomain (E ⊗[R] (R ⊗[K] F)) := by
    letI : Algebra (R ⊗[K] F) (E ⊗[R] (R ⊗[K] F)) := Algebra.TensorProduct.rightAlgebra
    have := IsLocalization.tensorRight (R := R) (S := R ⊗[K] F) (A := E) (nonZeroDivisors R)
    refine IsLocalization.isDomain_of_le_nonZeroDivisors (R := R ⊗[K] F)
      (M := Algebra.algebraMapSubmonoid (R ⊗[K] F) (nonZeroDivisors R)) (E ⊗[R] (R ⊗[K] F)) ?_
    rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    have hinj : Function.Injective (algebraMap R (R ⊗[K] F)) :=
      Algebra.TensorProduct.includeLeft_injective (S := R) (RingHom.injective (algebraMap K F))
    exact nonZeroDivisors.ne_zero hr (hinj (by simpa using h0))

  have : IsDomain (E ⊗[K] F) :=
    (Algebra.TensorProduct.cancelBaseChange K R R E F).symm.toMulEquiv.isDomain

  have : Algebra.FormallyEtale E L := Algebra.FormallyEtale.of_isSeparable E L
  have : Algebra.EssFiniteType E L := Algebra.EssFiniteType.of_comp K E L
  have := isReduced_tensor_domain_of_formallyEtale E L (E ⊗[K] F)
  exact isReduced_of_injective (Algebra.TensorProduct.cancelBaseChange K E E L F).symm
    (AlgEquiv.injective _)

/- English proof (translation)
Establish `: Algebra.EssFiniteType A (FractionRing A)` using `.of_isLocalization _ (nonZeroDivisors A)`. Establish `: Algebra.EssFiniteType K (FractionRing A)` using `.comp K A _`. Use `isReduced_tensor_field_of_perfectField K (FractionRing A) F` as an intermediate fact. Establish `: IsReduced (F ⊗[K] FractionRing A)` using `isReduced_of_injective (Algebra.TensorProduct.comm K F (FractionRing A)) (AlgEquiv.injective _)`. Conclude with `isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id K F) (IsScalarTower.toAlgHom K A (FractionRing A))) (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective A _))`.
-/
theorem isReduced_tensor_domain_of_perfectField (K A F : Type*) [Field K] [PerfectField K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Field F] [Algebra K F] :
    IsReduced (F ⊗[K] A) := by
  have : Algebra.EssFiniteType A (FractionRing A) :=
    .of_isLocalization _ (nonZeroDivisors A)
  have : Algebra.EssFiniteType K (FractionRing A) := .comp K A _
  have := isReduced_tensor_field_of_perfectField K (FractionRing A) F
  have : IsReduced (F ⊗[K] FractionRing A) :=
    isReduced_of_injective (Algebra.TensorProduct.comm K F (FractionRing A)) (AlgEquiv.injective _)
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id K F) (IsScalarTower.toAlgHom K A (FractionRing A)))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective A _))

/- English proof (translation)
Rewrite using `[Ideal.isRadical_iff_quotient_reduced]`. Set `e₀` to `MvPolynomial.algebraTensorAlgEquiv (σ := σ) K F`. Establish `hJ : Q.map (MvPolynomial.map (algebraMap K F)) = (Q.map (Algebra.TensorProduct.includeRight (R` using `K) (A := F)).toRingHom).map e₀.toRingEquiv.toRingHom := by`. Rewrite using `[Ideal.map_map]`. Use `congr 1`.

Use `RingHom.ext fun p => ?_` and prove the remaining obligations. Simplify using `[e₀, MvPolynomial.algebraTensorAlgEquiv_tmul]`. Set `e : F ⊗[K] (MvPolynomial σ K ⧸ Q) ≃+* MvPolynomial σ F ⧸ Q.map (MvPolynomial.map (algebraMap K F))` to `(Algebra.TensorProduct.tensorQuotientEquiv (R := K) K (MvPolynomial σ K) F Q).toRingEquiv.trans (Ideal.quotientEquiv _ _ e₀.toRingEquiv (hJ.trans rfl))`. Use `isReduced_tensor_domain_of_perfectField K (MvPolynomial σ K ⧸ Q) F` as an intermediate fact. Conclude with `isReduced_of_injective e.symm e.symm.injective`.
-/
theorem isRadical_map_of_isPrime_of_perfectField (K F : Type*) [Field K] [PerfectField K]
    [Field F] [Algebra K F] (σ : Type*) [Fintype σ] (Q : Ideal (MvPolynomial σ K))
    [Q.IsPrime] : (Q.map (MvPolynomial.map (algebraMap K F))).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  let e₀ := MvPolynomial.algebraTensorAlgEquiv (σ := σ) K F
  have hJ : Q.map (MvPolynomial.map (algebraMap K F)) =
      (Q.map (Algebra.TensorProduct.includeRight (R := K) (A := F)).toRingHom).map
        e₀.toRingEquiv.toRingHom := by
    rw [Ideal.map_map]
    congr 1
    refine RingHom.ext fun p => ?_
    simp [e₀, MvPolynomial.algebraTensorAlgEquiv_tmul]
  let e : F ⊗[K] (MvPolynomial σ K ⧸ Q) ≃+*
      MvPolynomial σ F ⧸ Q.map (MvPolynomial.map (algebraMap K F)) :=
    (Algebra.TensorProduct.tensorQuotientEquiv (R := K) K (MvPolynomial σ K) F Q).toRingEquiv.trans
      (Ideal.quotientEquiv _ _ e₀.toRingEquiv (hJ.trans rfl))
  have := isReduced_tensor_domain_of_perfectField K (MvPolynomial σ K ⧸ Q) F
  exact isReduced_of_injective e.symm e.symm.injective

/- English proof (translation)
Introduce `σ _ P hP`. Distinguish the cases in `hZ : ∃ n : ℤ, n ≠ 0 ∧ C n ∈ P`. Take `⟨n, hn, hnP⟩` from `hZ`. Establish `htop : P.map (MvPolynomial.map (Int.castRingHom ℂ)) = ⊤`. Apply `Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hnP)` to reduce the goal to its premises.

Rewrite using `[MvPolynomial.map_C]`. Conclude with `(isUnit_iff_ne_zero.mpr (by simpa using hn)).map C`. Rewrite using `[htop]`. Conclude with `fun x _ => Submodule.mem_top`. Use `push Not at hZ`.

Set `_` to `MvPolynomial.algebraMvPolynomial (σ := σ) (R := ℤ) (S := ℚ)`. Set `M` to `(nonZeroDivisors ℤ).map (C (σ := σ) (R := ℤ))`. Establish `: IsLocalization M (MvPolynomial σ ℚ)` using `MvPolynomial.isLocalization _ _`. Set `Q` to `P.map (algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ))`. Establish `hQ : Q.IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint M _ P hP (by`.

Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨n, hn, rfl⟩ hnP`. Conclude with `hZ n (nonZeroDivisors.ne_zero hn) hnP)`. Establish `hmap : P.map (MvPolynomial.map (Int.castRingHom ℂ)) = Q.map (MvPolynomial.map (algebraMap ℚ ℂ))`. Rewrite using `[Ideal.map_map]`.

Use `congr 1`. Use `RingHom.ext fun p => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = MvPolynomial.map (algebraMap ℚ ℂ) (MvPolynomial.map (algebraMap ℤ ℚ) p)`. Rewrite using `[MvPolynomial.map_map, show (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ from RingHom.ext_int _ _]`. Rewrite using `[hmap]`.

Conclude with `isRadical_map_of_isPrime_of_perfectField ℚ ℂ σ Q`.
-/
theorem PrimeComplexRadical.proof : PrimeComplexRadical.Statement := by
  intro σ _ P hP
  by_cases hZ : ∃ n : ℤ, n ≠ 0 ∧ C n ∈ P
  · obtain ⟨n, hn, hnP⟩ := hZ
    have htop : P.map (MvPolynomial.map (Int.castRingHom ℂ)) = ⊤ := by
      apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hnP)
      rw [MvPolynomial.map_C]
      exact (isUnit_iff_ne_zero.mpr (by simpa using hn)).map C
    rw [htop]
    exact fun x _ => Submodule.mem_top
  · push Not at hZ
    let _ := MvPolynomial.algebraMvPolynomial (σ := σ) (R := ℤ) (S := ℚ)
    let M := (nonZeroDivisors ℤ).map (C (σ := σ) (R := ℤ))
    have : IsLocalization M (MvPolynomial σ ℚ) := MvPolynomial.isLocalization _ _
    let Q := P.map (algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ))
    have hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P hP (by
      rw [Set.disjoint_left]
      rintro _ ⟨n, hn, rfl⟩ hnP
      exact hZ n (nonZeroDivisors.ne_zero hn) hnP)
    have hmap : P.map (MvPolynomial.map (Int.castRingHom ℂ)) =
        Q.map (MvPolynomial.map (algebraMap ℚ ℂ)) := by
      rw [Ideal.map_map]
      congr 1
      refine RingHom.ext fun p => ?_
      change _ = MvPolynomial.map (algebraMap ℚ ℂ) (MvPolynomial.map (algebraMap ℤ ℚ) p)
      rw [MvPolynomial.map_map,
        show (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ from RingHom.ext_int _ _]
    rw [hmap]
    exact isRadical_map_of_isPrime_of_perfectField ℚ ℂ σ Q

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
