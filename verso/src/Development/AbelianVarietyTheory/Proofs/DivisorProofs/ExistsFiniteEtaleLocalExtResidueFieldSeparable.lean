import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ hR k' _ _ _ _`. Take `⟨hN, -, hIC, hC⟩` from `hR`. Use `haveI := hN`. Use `haveI := hIC`. Use `haveI := hC`.

Take `⟨A, _, _, hfin, het, hloc, ⟨ε⟩⟩` from `GlobalTheory.exists_etale_lift_of_isSeparable R k'`. Use `haveI : IsLocalHom (algebraMap R A) := ((local_hom_TFAE (algebraMap R A)).out 0 4).mpr (comap_eq_maximalIdeal_of_finite _)`. Establish `hm : (maximalIdeal R).map (algebraMap R A) = maximalIdeal A` using `Algebra.FormallyUnramified.map_maximalIdeal`. Take `⟨hD, hI⟩` from `GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale R (maximalIdeal A) (Localization.AtPrime (maximalIdeal A))`. Set `e` to `IsLocalization.atUnits A (maximalIdeal A).primeCompl (S := Localization.AtPrime (maximalIdeal A)) (fun y hy => by`.

Rewrite using `[IsUnit.mem_submonoid_iff]`. Assume the negation of the conclusion as `h`. Conclude with `hy ((IsLocalRing.mem_maximalIdeal y).mpr h))`. Use `haveI : IsDomain A := e.toMulEquiv.isDomain`. Use `haveI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv.symm`.

Use `haveI : IsNoetherian R A := inferInstance`. Use `haveI : IsNoetherianRing A := isNoetherian_of_tower R inferInstance`. Set `g2 : ResidueField R ⊗[R] A →ₐ[R] ResidueField A` to `Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R (ResidueField R) (ResidueField A)) (IsScalarTower.toAlgHom R A (ResidueField A)) (fun _ _ => Commute.all _ _)`. Set `σ : k' →+* ResidueField A` to `g2.toRingHom.comp ε.symm.toRingHom`. Use `⟨A, inferInstance, inferInstance, inferInstance, algebraMap R A, σ, ⟨⟨inferInstance, inferInstance, inferInstance, ?_⟩, ?_, RingHom.finite_algebraMap.mpr hfin⟩, RingHom.etale_algebraMap.mpr het, ?_⟩` and prove the remaining obligations.

Use `GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal R) A` as an intermediate fact. Rewrite `this` using `[hm]`. Then use the resulting hypothesis. Use `haveI : Module.Free R A := Module.free_of_flat_of_isLocalRing`. Introduce `x y hxy`. Rewrite using `[← sub_eq_zero]`.

Establish `h0 : (x - y) • (1 : A) = 0`. Rewrite using `[Algebra.smul_def, _root_.mul_one, map_sub, hxy, sub_self]`. Conclude with `(smul_eq_zero.mp h0).resolve_right one_ne_zero`. Use extensionality with `r`. Simplify using `only [RingHom.comp_apply, σ, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, AlgHom.toRingHom_eq_coe]`.

Express the relevant statement in the definitionally equal form `g2 (algebraMap (ResidueField R) (ResidueField R ⊗[R] A) (residue R r)) = _`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply]`. Simplify using `[g2]`.
-/
theorem exists_finExt_etale_of_isSeparable : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R],
    AdmBase R (maximalIdeal R) → ∀ (k' : Type) [Field k'] [Algebra (ResidueField R) k']
    [Module.Finite (ResidueField R) k'] [Algebra.IsSeparable (ResidueField R) k'],
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R')
      (σ : k' →+* ResidueField R'), FinExt ρ ∧ ρ.Etale ∧
      σ.comp ((algebraMap (ResidueField R) k').comp (residue R)) = (residue R').comp ρ := by
  intro R _ _ _ hR k' _ _ _ _
  obtain ⟨hN, -, hIC, hC⟩ := hR
  haveI := hN; haveI := hIC; haveI := hC
  obtain ⟨A, _, _, hfin, het, hloc, ⟨ε⟩⟩ := GlobalTheory.exists_etale_lift_of_isSeparable R k'
  haveI : IsLocalHom (algebraMap R A) :=
    ((local_hom_TFAE (algebraMap R A)).out 0 4).mpr (comap_eq_maximalIdeal_of_finite _)
  have hm : (maximalIdeal R).map (algebraMap R A) = maximalIdeal A :=
    Algebra.FormallyUnramified.map_maximalIdeal
  obtain ⟨hD, hI⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale R (maximalIdeal A)
    (Localization.AtPrime (maximalIdeal A))
  let e := IsLocalization.atUnits A (maximalIdeal A).primeCompl
    (S := Localization.AtPrime (maximalIdeal A)) (fun y hy => by
      rw [IsUnit.mem_submonoid_iff]
      by_contra h
      exact hy ((IsLocalRing.mem_maximalIdeal y).mpr h))
  haveI : IsDomain A := e.toMulEquiv.isDomain
  haveI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv.symm
  haveI : IsNoetherian R A := inferInstance
  haveI : IsNoetherianRing A := isNoetherian_of_tower R inferInstance
  let g2 : ResidueField R ⊗[R] A →ₐ[R] ResidueField A :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R (ResidueField R) (ResidueField A))
      (IsScalarTower.toAlgHom R A (ResidueField A)) (fun _ _ => Commute.all _ _)
  let σ : k' →+* ResidueField A := g2.toRingHom.comp ε.symm.toRingHom
  refine ⟨A, inferInstance, inferInstance, inferInstance, algebraMap R A, σ,
    ⟨⟨inferInstance, inferInstance, inferInstance, ?_⟩, ?_, RingHom.finite_algebraMap.mpr hfin⟩,
    RingHom.etale_algebraMap.mpr het, ?_⟩
  · have := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal R) A
    rwa [hm] at this
  · haveI : Module.Free R A := Module.free_of_flat_of_isLocalRing
    intro x y hxy
    rw [← sub_eq_zero]
    have h0 : (x - y) • (1 : A) = 0 := by
      rw [Algebra.smul_def, _root_.mul_one, map_sub, hxy, sub_self]
    exact (smul_eq_zero.mp h0).resolve_right one_ne_zero
  · ext r
    simp only [RingHom.comp_apply, σ, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, AlgHom.toRingHom_eq_coe]
    change g2 (algebraMap (ResidueField R) (ResidueField R ⊗[R] A) (residue R r)) = _
    rw [Algebra.TensorProduct.algebraMap_apply]
    simp [g2]

end GlobalTheory.Mum
