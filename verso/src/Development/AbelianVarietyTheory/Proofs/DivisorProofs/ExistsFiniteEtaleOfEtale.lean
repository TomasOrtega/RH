import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HensNbhd

/- English proof (translation)
Set `Aq` to `Localization.AtPrime q`. Use `haveI : IsLocalHom (algebraMap R Aq) := by`. Use `⟨fun r hr => ?_⟩` and prove the remaining obligations. Rewrite `hr` using `[IsScalarTower.algebraMap_apply R A Aq, IsLocalization.AtPrime.isUnit_to_map_iff Aq q]`. Rewrite using `[← IsLocalRing.notMem_maximalIdeal, ← hq]`.

Conclude with `hr`. Use `haveI : Algebra.FormallyUnramified R Aq := Algebra.FormallyUnramified.comp R A Aq`. Use `haveI : Algebra.EssFiniteType R Aq := Algebra.EssFiniteType.comp R A Aq`. Take `⟨R', _, _, hfin, het, hloc, ⟨ε⟩⟩` from `exists_etale_lift_of_isSeparable R (ResidueField Aq)`. Use `haveI : HenselianLocalRing R' := henselianLocalRing_of_finite R R'`.

Use `haveI : IsLocalHom (algebraMap R R') := ((local_hom_TFAE (algebraMap R R')).out 0 4).mpr (comap_eq_maximalIdeal_of_finite _)`. Set `g1 : A →ₐ[R] ResidueField Aq` to `(IsScalarTower.toAlgHom R Aq (ResidueField Aq)).comp (IsScalarTower.toAlgHom R A Aq)`. Set `g2 : ResidueField R ⊗[R] R' →ₐ[R] ResidueField R'` to `Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R (ResidueField R) (ResidueField R')) (IsScalarTower.toAlgHom R R' (ResidueField R')) (fun _ _ => Commute.all _ _)`. Set `φ : A →ₐ[R] R' ⧸ maximalIdeal R'` to `(g2.comp (ε.symm.restrictScalars R).toAlgHom).comp g1`. Take `⟨ψ, -⟩` from `exists_algHom_lift_of_etale_of_isLocalRing (maximalIdeal R') φ`.

Establish `hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R'` using `Algebra.FormallyUnramified.map_maximalIdeal`. Use `⟨R', inferInstance, inferInstance, algebraMap R R', inferInstance, RingHom.finite_algebraMap.mpr hfin, ?_, hm, ?_, fun hc => ?_, ψ.toRingHom, ψ.comp_algebraMap⟩` and prove the remaining obligations. Conclude with `RingHom.etale_algebraMap.mpr het`. Establish `h : (ResidueField.map (algebraMap R R')).toAlgebra = (inferInstance : Algebra (ResidueField R) (ResidueField R'))` using `Algebra.algebra_ext _ _ fun r => by`. Take `⟨x, rfl⟩` from `residue_surjective r`.

Both sides reduce to the same expression. Conclude with `h ▸ (inferInstance : Algebra.IsSeparable (ResidueField R) (ResidueField R'))`. Use `isAdicComplete_map_of_finite (maximalIdeal R) R'` as an intermediate fact. Rewrite `this` using `[hm]`. Then use the resulting hypothesis.
-/
theorem exists_finite_etale_of_etale (R : Type) [CommRing R] [HenselianLocalRing R]
    [IsNoetherianRing R] (A : Type) [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (q : Ideal A) [q.IsPrime] (hq : q.comap (algebraMap R A) = maximalIdeal R) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (ρ : R →+* R') (_ : IsLocalHom ρ),
      ρ.Finite ∧ ρ.Etale ∧ (maximalIdeal R).map ρ = maximalIdeal R' ∧
      (letI := (ResidueField.map ρ).toAlgebra; Algebra.IsSeparable (ResidueField R) (ResidueField R')) ∧
      (IsAdicComplete (maximalIdeal R) R → IsAdicComplete (maximalIdeal R') R') ∧
      ∃ ψ : A →+* R', ψ.comp (algebraMap R A) = ρ := by
  let Aq := Localization.AtPrime q
  haveI : IsLocalHom (algebraMap R Aq) := by
    refine ⟨fun r hr => ?_⟩
    rw [IsScalarTower.algebraMap_apply R A Aq, IsLocalization.AtPrime.isUnit_to_map_iff Aq q] at hr
    rw [← IsLocalRing.notMem_maximalIdeal, ← hq]
    exact hr
  haveI : Algebra.FormallyUnramified R Aq := Algebra.FormallyUnramified.comp R A Aq
  haveI : Algebra.EssFiniteType R Aq := Algebra.EssFiniteType.comp R A Aq
  obtain ⟨R', _, _, hfin, het, hloc, ⟨ε⟩⟩ := exists_etale_lift_of_isSeparable R (ResidueField Aq)
  haveI : HenselianLocalRing R' := henselianLocalRing_of_finite R R'
  haveI : IsLocalHom (algebraMap R R') :=
    ((local_hom_TFAE (algebraMap R R')).out 0 4).mpr (comap_eq_maximalIdeal_of_finite _)
  let g1 : A →ₐ[R] ResidueField Aq :=
    (IsScalarTower.toAlgHom R Aq (ResidueField Aq)).comp (IsScalarTower.toAlgHom R A Aq)
  let g2 : ResidueField R ⊗[R] R' →ₐ[R] ResidueField R' :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R (ResidueField R) (ResidueField R'))
      (IsScalarTower.toAlgHom R R' (ResidueField R')) (fun _ _ => Commute.all _ _)
  let φ : A →ₐ[R] R' ⧸ maximalIdeal R' := (g2.comp (ε.symm.restrictScalars R).toAlgHom).comp g1
  obtain ⟨ψ, -⟩ := exists_algHom_lift_of_etale_of_isLocalRing (maximalIdeal R') φ
  have hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R' :=
    Algebra.FormallyUnramified.map_maximalIdeal
  refine ⟨R', inferInstance, inferInstance, algebraMap R R', inferInstance,
    RingHom.finite_algebraMap.mpr hfin, ?_, hm, ?_, fun hc => ?_, ψ.toRingHom, ψ.comp_algebraMap⟩
  · exact RingHom.etale_algebraMap.mpr het
  · have h : (ResidueField.map (algebraMap R R')).toAlgebra =
        (inferInstance : Algebra (ResidueField R) (ResidueField R')) :=
      Algebra.algebra_ext _ _ fun r => by
        obtain ⟨x, rfl⟩ := residue_surjective r
        rfl
    exact h ▸ (inferInstance : Algebra.IsSeparable (ResidueField R) (ResidueField R'))
  · have := isAdicComplete_map_of_finite (maximalIdeal R) R'
    rwa [hm] at this

/- English proof (translation)
Introduce `R _ _ _ U u hu ⟨s, hs⟩`. Take `⟨V, hV, hsV, -⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) (show s ∈ (⊤ : U.Opens) from trivial)`. Establish `hV' : IsAffineOpen V` using `hV`. Take `⟨t, rfl⟩ : s ∈ Set.range hV'.fromSpec` from `by rw [hV'.range_fromSpec]; exact hsV`. Set `f` to `hV'.fromSpec ≫ u`.

Establish `hf : Etale f` using `inferInstance`. Set `φ` to `Spec.preimage f`. Establish `hφ : Spec.map φ = f` using `Spec.map_preimage f`. Establish `het : RingHom.Etale φ.hom`. Rewrite using `[← HasRingHomProperty.Spec_iff (P := @Etale), hφ]`.

Conclude with `hf`. Use `letI := φ.hom.toAlgebra`. Use `haveI : Algebra.Etale R Γ(U, V) := het`. Establish `hq : t.asIdeal.comap (algebraMap R Γ(U, V)) = maximalIdeal R`. Establish `h1 : (Spec.map φ) t = closedPoint R`.

Rewrite using `[hφ, ← hs]`. Both sides reduce to the same expression. Conclude with `congrArg PrimeSpectrum.asIdeal h1`. Use `haveI : t.asIdeal.IsPrime := t.isPrime`. Take `⟨R', i1, i2, ρ, i3, h1, h2, h3, h4, h5, ψ, hψ⟩` from `exists_finite_etale_of_etale R Γ(U, V) t.asIdeal hq`.

Use `⟨R', i1, i2, ρ, i3, h1, h2, h3, h4, h5, Spec.map (CommRingCat.ofHom ψ) ≫ hV'.fromSpec, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc]`. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom ψ) ≫ f = _`. Rewrite using `[← hφ, ← Spec.map_comp, ← hψ]`. Both sides reduce to the same expression.
-/
theorem exists_finite_etale_section : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] [IsNoetherianRing R] (U : Scheme.{0}) (u : U ⟶ Sp R),
    Etale u → closedPoint R ∈ Set.range u →
    ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (ρ : R →+* R') (_ : IsLocalHom ρ),
      ρ.Finite ∧ ρ.Etale ∧ (maximalIdeal R).map ρ = maximalIdeal R' ∧
      (letI := (ResidueField.map ρ).toAlgebra; Algebra.IsSeparable (ResidueField R) (ResidueField R')) ∧
      (IsAdicComplete (maximalIdeal R) R → IsAdicComplete (maximalIdeal R') R') ∧
      ∃ σ : Sp R' ⟶ U, σ ≫ u = spMap ρ := by
  intro R _ _ _ U u hu ⟨s, hs⟩
  obtain ⟨V, hV, hsV, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) (show s ∈ (⊤ : U.Opens) from trivial)
  have hV' : IsAffineOpen V := hV
  obtain ⟨t, rfl⟩ : s ∈ Set.range hV'.fromSpec := by rw [hV'.range_fromSpec]; exact hsV
  let f := hV'.fromSpec ≫ u
  have hf : Etale f := inferInstance
  let φ := Spec.preimage f
  have hφ : Spec.map φ = f := Spec.map_preimage f
  have het : RingHom.Etale φ.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hφ]; exact hf
  letI := φ.hom.toAlgebra
  haveI : Algebra.Etale R Γ(U, V) := het
  have hq : t.asIdeal.comap (algebraMap R Γ(U, V)) = maximalIdeal R := by
    have h1 : (Spec.map φ) t = closedPoint R := by
      rw [hφ, ← hs]; rfl
    exact congrArg PrimeSpectrum.asIdeal h1
  haveI : t.asIdeal.IsPrime := t.isPrime
  obtain ⟨R', i1, i2, ρ, i3, h1, h2, h3, h4, h5, ψ, hψ⟩ :=
    exists_finite_etale_of_etale R Γ(U, V) t.asIdeal hq
  refine ⟨R', i1, i2, ρ, i3, h1, h2, h3, h4, h5, Spec.map (CommRingCat.ofHom ψ) ≫ hV'.fromSpec, ?_⟩
  rw [Category.assoc]
  change Spec.map (CommRingCat.ofHom ψ) ≫ f = _
  rw [← hφ, ← Spec.map_comp, ← hψ]
  rfl

end GlobalTheory.HensNbhd
