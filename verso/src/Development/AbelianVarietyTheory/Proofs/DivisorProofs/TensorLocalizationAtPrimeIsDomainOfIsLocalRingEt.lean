import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `P R E _ _ _ _ _ _ _ _ Q _ hloc`. Use `letI : Algebra (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q) := (Algebra.TensorProduct.map (AlgHom.id P R) (IsScalarTower.toAlgHom P E (Localization.AtPrime Q))).toAlgebra`. Use `haveI : IsScalarTower R (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q) := .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]`. Use `haveI hl := IsLocalization.tensorProduct_tensorProduct_right P R Q.primeCompl (Localization.AtPrime Q) (by ext; simp [RingHom.algebraMap_toAlgebra])`. Set `𝔭 : Ideal (R ⊗[P] E)` to `(maximalIdeal (R ⊗[P] Localization.AtPrime Q)).comap (algebraMap (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q))`.

Use `haveI : 𝔭.IsPrime := Ideal.comap_isPrime _ _`. Establish `hle : Q.primeCompl.map (Algebra.TensorProduct.includeRight (R` using `P) (A := R)) ≤ 𝔭.primeCompl := by`. Introduce `x hx`. Establish `hu` using `IsLocalization.map_units (R ⊗[P] Localization.AtPrime Q) (⟨x, hx⟩ : Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := P) (A := R)))`. Introduce `h`.

Conclude with `((mem_maximalIdeal _).mp (Ideal.mem_comap.mp h)) hu`. Use `haveI : IsLocalization 𝔭.primeCompl (R ⊗[P] Localization.AtPrime Q) := IsLocalization.of_le _ _ hle (fun r hr => by`. Assume the negation of the conclusion as `hu`. Conclude with `hr (Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr hu)))`. Take `⟨hd, -⟩` from `etale_localization_atPrime_isDomain_isIntegrallyClosed R (R ⊗[P] E) 𝔭`.

Set `e : Localization.AtPrime 𝔭 ≃ₐ[R ⊗[P] E] (R ⊗[P] Localization.AtPrime Q)` to `IsLocalization.algEquiv 𝔭.primeCompl _ _`. Conclude with `e.symm.injective.isDomain _`.
-/
theorem tensor_localization_atPrime_isDomain_of_isLocalRing_etale :
    ∀ (P R E : Type) [CommRing P] [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra P R]
      [CommRing E] [Algebra P E] [Algebra.Etale P E] (Q : Ideal E) [Q.IsPrime],
      IsLocalRing (TensorProduct P R (Localization.AtPrime Q)) →
        IsDomain (TensorProduct P R (Localization.AtPrime Q)) := by
  intro P R E _ _ _ _ _ _ _ _ Q _ hloc
  letI : Algebra (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q) :=
    (Algebra.TensorProduct.map (AlgHom.id P R)
      (IsScalarTower.toAlgHom P E (Localization.AtPrime Q))).toAlgebra
  haveI : IsScalarTower R (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI hl := IsLocalization.tensorProduct_tensorProduct_right P R Q.primeCompl
    (Localization.AtPrime Q) (by ext; simp [RingHom.algebraMap_toAlgebra])
  let 𝔭 : Ideal (R ⊗[P] E) :=
    (maximalIdeal (R ⊗[P] Localization.AtPrime Q)).comap
      (algebraMap (R ⊗[P] E) (R ⊗[P] Localization.AtPrime Q))
  haveI : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have hle : Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := P) (A := R)) ≤
      𝔭.primeCompl := by
    intro x hx
    have hu := IsLocalization.map_units (R ⊗[P] Localization.AtPrime Q)
      (⟨x, hx⟩ : Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := P) (A := R)))
    intro h
    exact ((mem_maximalIdeal _).mp (Ideal.mem_comap.mp h)) hu
  haveI : IsLocalization 𝔭.primeCompl (R ⊗[P] Localization.AtPrime Q) :=
    IsLocalization.of_le _ _ hle (fun r hr => by
      by_contra hu
      exact hr (Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr hu)))
  obtain ⟨hd, -⟩ := etale_localization_atPrime_isDomain_isIntegrallyClosed R (R ⊗[P] E) 𝔭
  let e : Localization.AtPrime 𝔭 ≃ₐ[R ⊗[P] E] (R ⊗[P] Localization.AtPrime Q) :=
    IsLocalization.algEquiv 𝔭.primeCompl _ _
  exact e.symm.injective.isDomain _

end GlobalTheory
