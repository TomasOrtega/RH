import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorIsLocalRingOfUniquePrimeOverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLocalizationAtPrimeIsDomainOfIsLocalRingEtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubMemMaximalIdealEtaleOverOriginStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalDomainOverHenselianPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdealUniquePrimeOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorKernelMemMapIdeal
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.OriginPrimes

/- English proof (translation)
Introduce `A' _ _ _ 𝔭 _ E _ _ _ Q _ hQ`. Take `⟨S, _, _, _, _, f, hfi, hker⟩` from `GlobalTheory.T.exists_normal_local_domain_over_henselian_prime A' 𝔭`. Take `⟨hXi, hOp, hOc, hOu⟩` from `GlobalTheory.T.origin_ideal_unique_prime_over A' S f hfi`. Use `letI : Algebra (Polynomial A') (Polynomial S) := (Polynomial.mapRingHom f).toAlgebra`. Use `haveI : Algebra.IsIntegral (Polynomial A') (Polynomial S) := ⟨hXi⟩`.

Establish `hmax : (maximalIdeal (Localization.AtPrime Q)).comap (algebraMap (Polynomial A') (Localization.AtPrime Q)) = GlobalTheory.KeyOriginCut.originIdeal A'`. Establish `h0 : (maximalIdeal (Localization.AtPrime Q)).comap (algebraMap E (Localization.AtPrime Q)) = Q` using `Localization.AtPrime.comap_maximalIdeal (I := Q)`. Rewrite using `[IsScalarTower.algebraMap_eq (Polynomial A') E (Localization.AtPrime Q), ← Ideal.comap_comap, h0, hQ]`. Use `haveI hloc : IsLocalRing (TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q)) := GlobalTheory.T.isLocalRing_tensor_of_unique_prime_over (Polynomial A') (Polynomial S) (Localization.AtPrime Q) (GlobalTheory.KeyOriginCut.originIdeal S) (by rw [hmax]; exact hOc) ( …`. Use `haveI hdom : IsDomain (TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q)) := GlobalTheory.T.isDomain_tensor_atPrime_of_isLocalRing_of_etale (Polynomial A') (Polynomial S) E Q hloc`.

Use `haveI : Module.Flat (Polynomial A') (Localization.AtPrime Q) := Module.Flat.trans (Polynomial A') E (Localization.AtPrime Q)`. Establish `hkerX : RingHom.ker (algebraMap (Polynomial A') (Polynomial S)) = 𝔭.map Polynomial.C`. Express the relevant statement in the definitionally equal form `RingHom.ker (Polynomial.mapRingHom f) = _`. Rewrite using `[Polynomial.ker_mapRingHom, hker]`. Establish `hJ : 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C) = (𝔭.map Polynomial.C).map (algebraMap (Polynomial A') (Localization.AtPrime Q))`.

Rewrite using `[Ideal.map_map]`. Set `g : Localization.AtPrime Q →+* TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q)` to `(Algebra.TensorProduct.includeRight : Localization.AtPrime Q →ₐ[Polynomial A'] _).toRingHom`. Establish `hg0 : ∀ y ∈ 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C), g y = 0`. Rewrite using `[hJ]`. Establish `hle : (𝔭.map Polynomial.C).map (algebraMap (Polynomial A') (Localization.AtPrime Q)) ≤ RingHom.ker g`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `m hm`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `(Algebra.TensorProduct.includeRight : Localization.AtPrime Q →ₐ[Polynomial A'] _) (algebraMap (Polynomial A') (Localization.AtPrime Q) m) = 0`. Rewrite using `[AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]`.

Establish `: algebraMap (Polynomial A') (Polynomial S) m = 0`. Rewrite using `[← RingHom.mem_ker, hkerX]`. Conclude with `hm`. Rewrite using `[this, TensorProduct.zero_tmul]`. Conclude with `fun y hy => hle hy`.

Establish `hg1 : ∀ y, g y = 0 → y ∈ 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C)`. Introduce `y hy`. Rewrite using `[hJ]`. Conclude with `GlobalTheory.T.flat_tensor_kernel_mem_map_ideal (Polynomial A') (Polynomial S) (Localization.AtPrime Q) _ hkerX y hy`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `htop`. Establish `h1` using `hg0 1 (by rw [htop]; exact Submodule.mem_top)`. Rewrite `h1` using `[map_one]`. Conclude with `one_ne_zero h1`. Introduce `x y hxy`.

Establish `h` using `hg0 _ hxy`. Rewrite `h` using `[map_mul]`. Break down `mul_eq_zero.mp h with h | h` into its components or cases. Conclude with `Or.inl (hg1 x h)`. Conclude with `Or.inr (hg1 y h)`.
-/
theorem origin_primes : ∀ (A' : Type) [CommRing A'] [HenselianLocalRing A'] [IsSepClosed (ResidueField A')]
    (𝔭 : Ideal A') [𝔭.IsPrime] (E : Type) [CommRing E] [Algebra (Polynomial A') E]
    [Algebra.Etale (Polynomial A') E] (Q : Ideal E) [Q.IsPrime],
    Q.comap (algebraMap (Polynomial A') E) = GlobalTheory.KeyOriginCut.originIdeal A' →
    (𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C)).IsPrime := by
  intro A' _ _ _ 𝔭 _ E _ _ _ Q _ hQ
  obtain ⟨S, _, _, _, _, f, hfi, hker⟩ := GlobalTheory.T.exists_normal_local_domain_over_henselian_prime A' 𝔭
  obtain ⟨hXi, hOp, hOc, hOu⟩ := GlobalTheory.T.origin_ideal_unique_prime_over A' S f hfi
  letI : Algebra (Polynomial A') (Polynomial S) := (Polynomial.mapRingHom f).toAlgebra
  haveI : Algebra.IsIntegral (Polynomial A') (Polynomial S) := ⟨hXi⟩
  have hmax : (maximalIdeal (Localization.AtPrime Q)).comap
      (algebraMap (Polynomial A') (Localization.AtPrime Q)) = GlobalTheory.KeyOriginCut.originIdeal A' := by
    have h0 : (maximalIdeal (Localization.AtPrime Q)).comap (algebraMap E (Localization.AtPrime Q)) = Q :=
      Localization.AtPrime.comap_maximalIdeal (I := Q)
    rw [IsScalarTower.algebraMap_eq (Polynomial A') E (Localization.AtPrime Q), ← Ideal.comap_comap,
      h0, hQ]
  haveI hloc : IsLocalRing (TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q)) :=
    GlobalTheory.T.isLocalRing_tensor_of_unique_prime_over (Polynomial A') (Polynomial S) (Localization.AtPrime Q) (GlobalTheory.KeyOriginCut.originIdeal S)
      (by rw [hmax]; exact hOc) (by intro 𝔔 h1 h2; rw [hmax] at h2; exact hOu 𝔔 h1 h2)
      (GlobalTheory.T.exists_sub_mem_maximalIdeal_etale_over_origin A' E Q hQ)
  haveI hdom : IsDomain (TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q)) :=
    GlobalTheory.T.isDomain_tensor_atPrime_of_isLocalRing_of_etale (Polynomial A') (Polynomial S) E Q hloc
  haveI : Module.Flat (Polynomial A') (Localization.AtPrime Q) :=
    Module.Flat.trans (Polynomial A') E (Localization.AtPrime Q)
  have hkerX : RingHom.ker (algebraMap (Polynomial A') (Polynomial S)) = 𝔭.map Polynomial.C := by
    change RingHom.ker (Polynomial.mapRingHom f) = _
    rw [Polynomial.ker_mapRingHom, hker]
  have hJ : 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C) =
      (𝔭.map Polynomial.C).map (algebraMap (Polynomial A') (Localization.AtPrime Q)) := by
    rw [Ideal.map_map]
  let g : Localization.AtPrime Q →+* TensorProduct (Polynomial A') (Polynomial S) (Localization.AtPrime Q) :=
    (Algebra.TensorProduct.includeRight : Localization.AtPrime Q →ₐ[Polynomial A'] _).toRingHom
  have hg0 : ∀ y ∈ 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C), g y = 0 := by
    rw [hJ]
    have hle : (𝔭.map Polynomial.C).map (algebraMap (Polynomial A') (Localization.AtPrime Q)) ≤ RingHom.ker g := by
      rw [Ideal.map_le_iff_le_comap]
      intro m hm
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change (Algebra.TensorProduct.includeRight : Localization.AtPrime Q →ₐ[Polynomial A'] _)
        (algebraMap (Polynomial A') (Localization.AtPrime Q) m) = 0
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
      have : algebraMap (Polynomial A') (Polynomial S) m = 0 := by
        rw [← RingHom.mem_ker, hkerX]; exact hm
      rw [this, TensorProduct.zero_tmul]
    exact fun y hy => hle hy
  have hg1 : ∀ y, g y = 0 → y ∈ 𝔭.map ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C) := by
    intro y hy
    rw [hJ]
    exact GlobalTheory.T.flat_tensor_kernel_mem_map_ideal (Polynomial A') (Polynomial S) (Localization.AtPrime Q) _ hkerX y hy
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 := hg0 1 (by rw [htop]; exact Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  · intro x y hxy
    have h := hg0 _ hxy
    rw [map_mul] at h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (hg1 x h)
    · exact Or.inr (hg1 y h)

end GlobalTheory.OriginPrimes
