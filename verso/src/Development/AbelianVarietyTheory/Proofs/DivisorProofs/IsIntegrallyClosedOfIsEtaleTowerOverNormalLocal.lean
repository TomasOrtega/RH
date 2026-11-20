import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.EtNormal

/- English proof (translation)
Set `B` to `Algebra.EssFiniteType.subalgebra A T`. Set `P : Ideal B` to `(IsLocalRing.maximalIdeal T).comap (algebraMap B T)`. Use `haveI hP : P.IsPrime := Ideal.comap_isPrime _ _`. Establish `hM : Algebra.EssFiniteType.submonoid A T = P.primeCompl`. Use extensionality with `x`.

Express the relevant statement in the definitionally equal form `IsUnit (algebraMap B T x) ↔ x ∉ P`. Simplify using `[P, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Use `haveI hloc : IsLocalization.AtPrime T P := by`. Use `Algebra.EssFiniteType.isLocalization A T` as an intermediate fact. Rewrite `this` using `[hM]`.

Conclude with `this`. Use `haveI : Algebra.FinitePresentation A B := (Algebra.FinitePresentation.of_finiteType).1 inferInstance`. Set `e : T ≃ₐ[A] Localization.AtPrime P` to `(IsLocalization.algEquiv P.primeCompl T (Localization.AtPrime P)).restrictScalars A`. Use `haveI : Algebra.FormallySmooth A (Localization.AtPrime P) := Algebra.FormallySmooth.of_equiv e`. Use `haveI : Algebra.IsSmoothAt A P := inferInstance`.

Take `⟨f, hfP, n, _, _, _⟩` from `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := P)`. Use `isIntegrallyClosed_mvPolynomial_fin A n` as an intermediate fact. Use `isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers f) (Localization.Away f) P ?_ (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_etale (MvPolynomial (Fin n) A) q _) T` and prove the remaining obligations. Rewrite using `[Ideal.disjoint_powers_iff_notMem_of_isPrime]` and apply the resulting hypothesis.
-/
theorem isDomain_and_isIntegrallyClosed_of_formallyEtale (A T : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [IsNoetherianRing A] [CommRing T] [IsLocalRing T] [Algebra A T]
    [Algebra.FormallyEtale A T] [Algebra.EssFiniteType A T] :
    IsDomain T ∧ IsIntegrallyClosed T := by
  let B := Algebra.EssFiniteType.subalgebra A T
  let P : Ideal B := (IsLocalRing.maximalIdeal T).comap (algebraMap B T)
  haveI hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hM : Algebra.EssFiniteType.submonoid A T = P.primeCompl := by
    ext x
    change IsUnit (algebraMap B T x) ↔ x ∉ P
    simp [P, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  haveI hloc : IsLocalization.AtPrime T P := by
    have := Algebra.EssFiniteType.isLocalization A T
    rw [hM] at this
    exact this
  haveI : Algebra.FinitePresentation A B :=
    (Algebra.FinitePresentation.of_finiteType).1 inferInstance
  let e : T ≃ₐ[A] Localization.AtPrime P :=
    (IsLocalization.algEquiv P.primeCompl T (Localization.AtPrime P)).restrictScalars A
  haveI : Algebra.FormallySmooth A (Localization.AtPrime P) := Algebra.FormallySmooth.of_equiv e
  haveI : Algebra.IsSmoothAt A P := inferInstance
  obtain ⟨f, hfP, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := P)
  have := isIntegrallyClosed_mvPolynomial_fin A n
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers f)
    (Localization.Away f) P ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_etale (MvPolynomial (Fin n) A) q _) T
  rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]

end GlobalTheory.EtNormal

namespace GlobalTheory.FieldPair

/- English proof (translation)
Introduce `K L _ _ cK cL r R T ι ψ τ h`. Use `haveI := h.top.isLocalRing`. Use `haveI := h.normal`. Set `c0 : ℂ →+* R` to `cK.codRestrict R h.base.const_mem`. Set `cT : ℂ →+* T` to `cL.codRestrict T h.top.const_mem`.

Use `letI : Algebra ℂ R := c0.toAlgebra`. Use `haveI : Algebra.EssFiniteType ℂ R := h.base.essFiniteType`. Use `haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R`. Set `A` to `MvPolynomial (Fin r) R`. Set `φ : A →+* T` to `MvPolynomial.eval₂Hom ι τ`.

Use `letI : Algebra A T := φ.toAlgebra`. Use `letI : Algebra ℂ T := cT.toAlgebra`. Use `haveI : Algebra.FormallyEtale A T := h.etale`. Use `haveI : Algebra.EssFiniteType ℂ T := h.top.essFiniteType`. Use `haveI : IsScalarTower ℂ A T := by`.

Use `IsScalarTower.of_algebraMap_eq fun a => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `cT a = φ (MvPolynomial.C (c0 a))`. Establish `e : φ (MvPolynomial.C (c0 a)) = ι (c0 a)` using `MvPolynomial.eval₂Hom_C _ _ _`. Rewrite using `[e]`. Conclude with `Subtype.ext (h.const a).symm`.

Use `haveI : Algebra.EssFiniteType A T := Algebra.EssFiniteType.of_comp ℂ A T`. Use `haveI : IsIntegrallyClosed A := isIntegrallyClosed_mvPolynomial_fin R r`. Conclude with `(GlobalTheory.EtNormal.isDomain_and_isIntegrallyClosed_of_formallyEtale A T).2`.
-/
theorem isIntegrallyClosed_of_isEtTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T), IsEtTower cK R cL T ι ψ τ → IsIntegrallyClosed T := by
  intro K L _ _ cK cL r R T ι ψ τ h
  haveI := h.top.isLocalRing
  haveI := h.normal
  let c0 : ℂ →+* R := cK.codRestrict R h.base.const_mem
  let cT : ℂ →+* T := cL.codRestrict T h.top.const_mem
  letI : Algebra ℂ R := c0.toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := h.base.essFiniteType
  haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  let A := MvPolynomial (Fin r) R
  let φ : A →+* T := MvPolynomial.eval₂Hom ι τ
  letI : Algebra A T := φ.toAlgebra
  letI : Algebra ℂ T := cT.toAlgebra
  haveI : Algebra.FormallyEtale A T := h.etale
  haveI : Algebra.EssFiniteType ℂ T := h.top.essFiniteType
  haveI : IsScalarTower ℂ A T := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    change cT a = φ (MvPolynomial.C (c0 a))
    have e : φ (MvPolynomial.C (c0 a)) = ι (c0 a) := MvPolynomial.eval₂Hom_C _ _ _
    rw [e]
    exact Subtype.ext (h.const a).symm
  haveI : Algebra.EssFiniteType A T := Algebra.EssFiniteType.of_comp ℂ A T
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_mvPolynomial_fin R r
  exact (GlobalTheory.EtNormal.isDomain_and_isIntegrallyClosed_of_formallyEtale A T).2

end GlobalTheory.FieldPair
