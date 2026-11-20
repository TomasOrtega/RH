import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SepExt

open Polynomial

/- English proof (translation)
Use `set p := minpoly K a`. Establish `hp0 : p ≠ 0` using `minpoly.ne_zero ha.isIntegral`. Establish `hsplit : (p.map (algebraMap K Ω)).Splits` using `IsSepClosed.splits_codomain p ha`. Establish `hne : p.map (algebraMap K Ω') ≠ 0` using `(Polynomial.map_ne_zero_iff (algebraMap K Ω').injective).2 hp0`. Establish `himg` using `Splits.image_rootSet_of_map_ne_zero hsplit j hne`.

Establish `hroot : IsScalarTower.toAlgHom K L Ω' a ∈ p.rootSet Ω'`. Rewrite using `[mem_rootSet_of_ne hp0, aeval_algHom_apply, minpoly.aeval, map_zero]`. Rewrite `hroot` using `[← himg]`. Take `⟨w, -, hw⟩` from `hroot`. Conclude with `(AlgHom.mem_fieldRange).2 ⟨w, hw⟩`.
-/
theorem mem_fieldRange (K L Ω Ω' : Type) [Field K] [Field L] [Field Ω] [Field Ω'] [Algebra K L]
    [Algebra K Ω] [IsSepClosed Ω] [Algebra L Ω'] [Algebra K Ω'] [IsScalarTower K L Ω']
    (j : Ω →ₐ[K] Ω') (a : L) (ha : IsSeparable K a) :
    IsScalarTower.toAlgHom K L Ω' a ∈ j.fieldRange := by
  set p := minpoly K a
  have hp0 : p ≠ 0 := minpoly.ne_zero ha.isIntegral
  have hsplit : (p.map (algebraMap K Ω)).Splits := IsSepClosed.splits_codomain p ha
  have hne : p.map (algebraMap K Ω') ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K Ω').injective).2 hp0
  have himg := Splits.image_rootSet_of_map_ne_zero hsplit j hne
  have hroot : IsScalarTower.toAlgHom K L Ω' a ∈ p.rootSet Ω' := by
    rw [mem_rootSet_of_ne hp0, aeval_algHom_apply, minpoly.aeval, map_zero]
  rw [← himg] at hroot
  obtain ⟨w, -, hw⟩ := hroot
  exact (AlgHom.mem_fieldRange).2 ⟨w, hw⟩

end GlobalTheory.SepExt

namespace GlobalTheory.SepExt

open Polynomial

/- English proof (translation)
Introduce `K L Ω Ω' _ _ _ _ _ _ _ _ _ _ _ _ j`. Use `haveI : IsSepClosed Ω := IsSepClosure.sep_closed K`. Set `Ls : IntermediateField K L` to `separableClosure K L`. Set `ψ : Ls →ₐ[K] Ω'` to `(IsScalarTower.toAlgHom K L Ω').comp Ls.val`. Establish `hmem : ∀ a : Ls, ψ a ∈ j.fieldRange` using `fun a => mem_fieldRange K L Ω Ω' j a ((mem_separableClosure_iff).1 a.2)`.

Set `e : Ω ≃ₐ[K] j.fieldRange` to `AlgEquiv.ofInjectiveField j`. Set `φ : Ls →ₐ[K] Ω` to `e.symm.toAlgHom.comp (ψ.codRestrict j.fieldRange.toSubalgebra hmem)`. Establish `hφ : ∀ a : Ls, j (φ a) = ψ a`. Introduce `a`. Establish `h` using `congrArg Subtype.val (e.apply_symm_apply ⟨ψ a, hmem a⟩)`.

Conclude with `h`. Set `E : IntermediateField K Ω` to `φ.fieldRange`. Establish `: FiniteDimensional K E` using `(AlgEquiv.ofInjectiveField φ).toLinearEquiv.finiteDimensional`. Establish `: Finite ((Ω ≃ₐ[K] Ω) ⧸ E.fixingSubgroup)` using `Subgroup.quotient_finite_of_isOpen _ E.fixingSubgroup_isOpen`. Use `⟨E.fixingSubgroup, Subgroup.finiteIndex_of_finite_quotient, fun σ hσ => ?_⟩` and prove the remaining obligations.

Set `A` to `AlgebraicClosure Ω'`. Use `letI : Algebra Ω A := ((algebraMap Ω' A).comp j.toRingHom).toAlgebra`. Use `haveI : IsScalarTower K Ω A := IsScalarTower.of_algebraMap_eq fun x => by`. Express the relevant statement in the definitionally equal form `algebraMap K A x = algebraMap Ω' A (j (algebraMap K Ω x))`. Rewrite using `[AlgHom.commutes, ← IsScalarTower.algebraMap_apply]`.

Use `haveI : Algebra.IsAlgebraic K Ω' := Algebra.IsAlgebraic.trans K L Ω'`. Use `haveI : IsAlgClosure K A := IsAlgClosure.ofAlgebraic K Ω' A`. Use `haveI : Normal K A := IsAlgClosure.normal K A`. Set `τ : A ≃ₐ[K] A` to `σ.liftNormal A`. Establish `hτ : ∀ x : Ω, τ (algebraMap Ω' A (j x)) = algebraMap Ω' A (j (σ x))` using `fun x => AlgEquiv.liftNormal_commutes σ A x`.

Establish `hfixL : ∀ a : L, τ (algebraMap L A a) = algebraMap L A a`. Establish `hinj` using `IsPurelyInseparable.injective_comp_algebraMap Ls L A`. Establish `heq : (τ.toRingEquiv.toRingHom.comp (algebraMap L A)).comp (algebraMap Ls L) = (algebraMap L A).comp (algebraMap Ls L)`. Use extensionality with `a`. Establish `h1 : algebraMap L A (algebraMap Ls L a) = algebraMap Ω' A (j (φ a))`.

Rewrite using `[hφ]`. Conclude with `IsScalarTower.algebraMap_apply L Ω' A _`. Establish `h2 : σ (φ a) = φ a` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ ⟨a, rfl⟩`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[h1]`.

Express the relevant statement in the definitionally equal form `τ (algebraMap Ω' A (j (φ a))) = _`. Rewrite using `[hτ, h2]`. Conclude with `fun a => congrArg (fun f : L →+* A => f a) (hinj heq)`. Set `τL : A ≃ₐ[L] A` to `{ τ.toRingEquiv with commutes' := hfixL }`. Use `⟨τL.restrictNormal Ω', fun x => ?_⟩` and prove the remaining obligations.

Apply `(algebraMap Ω' A).injective` to reduce the goal to its premises. Rewrite using `[AlgEquiv.restrictNormal_commutes]`. Conclude with `hτ x`.
-/
theorem exists_finiteIndex_extend : ∀ (K L Ω Ω' : Type) [Field K] [Field L] [Field Ω] [Field Ω'] [Algebra K L] [FiniteDimensional K L] [Algebra K Ω] [IsSepClosure K Ω] [Algebra L Ω'] [IsSepClosure L Ω'] [Algebra K Ω'] [IsScalarTower K L Ω'] (j : Ω →ₐ[K] Ω'), ∃ H : Subgroup (Ω ≃ₐ[K] Ω), H.FiniteIndex ∧ ∀ σ ∈ H, ∃ σ' : Ω' ≃ₐ[L] Ω', ∀ x, σ' (j x) = j (σ x) := by
  intro K L Ω Ω' _ _ _ _ _ _ _ _ _ _ _ _ j
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  let Ls : IntermediateField K L := separableClosure K L
  let ψ : Ls →ₐ[K] Ω' := (IsScalarTower.toAlgHom K L Ω').comp Ls.val
  have hmem : ∀ a : Ls, ψ a ∈ j.fieldRange := fun a =>
    mem_fieldRange K L Ω Ω' j a ((mem_separableClosure_iff).1 a.2)
  let e : Ω ≃ₐ[K] j.fieldRange := AlgEquiv.ofInjectiveField j
  let φ : Ls →ₐ[K] Ω := e.symm.toAlgHom.comp (ψ.codRestrict j.fieldRange.toSubalgebra hmem)
  have hφ : ∀ a : Ls, j (φ a) = ψ a := by
    intro a
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨ψ a, hmem a⟩)
    exact h
  let E : IntermediateField K Ω := φ.fieldRange
  have : FiniteDimensional K E :=
    (AlgEquiv.ofInjectiveField φ).toLinearEquiv.finiteDimensional
  have : Finite ((Ω ≃ₐ[K] Ω) ⧸ E.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ E.fixingSubgroup_isOpen
  refine ⟨E.fixingSubgroup, Subgroup.finiteIndex_of_finite_quotient, fun σ hσ => ?_⟩
  let A := AlgebraicClosure Ω'
  letI : Algebra Ω A := ((algebraMap Ω' A).comp j.toRingHom).toAlgebra
  haveI : IsScalarTower K Ω A := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap K A x = algebraMap Ω' A (j (algebraMap K Ω x))
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.IsAlgebraic K Ω' := Algebra.IsAlgebraic.trans K L Ω'
  haveI : IsAlgClosure K A := IsAlgClosure.ofAlgebraic K Ω' A
  haveI : Normal K A := IsAlgClosure.normal K A
  let τ : A ≃ₐ[K] A := σ.liftNormal A
  have hτ : ∀ x : Ω, τ (algebraMap Ω' A (j x)) = algebraMap Ω' A (j (σ x)) := fun x =>
    AlgEquiv.liftNormal_commutes σ A x
  have hfixL : ∀ a : L, τ (algebraMap L A a) = algebraMap L A a := by
    have hinj := IsPurelyInseparable.injective_comp_algebraMap Ls L A
    have heq : (τ.toRingEquiv.toRingHom.comp (algebraMap L A)).comp (algebraMap Ls L) =
        (algebraMap L A).comp (algebraMap Ls L) := by
      ext a
      have h1 : algebraMap L A (algebraMap Ls L a) = algebraMap Ω' A (j (φ a)) := by
        rw [hφ]; exact IsScalarTower.algebraMap_apply L Ω' A _
      have h2 : σ (φ a) = φ a :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ ⟨a, rfl⟩
      simp only [RingHom.comp_apply]
      rw [h1]
      change τ (algebraMap Ω' A (j (φ a))) = _
      rw [hτ, h2]
    exact fun a => congrArg (fun f : L →+* A => f a) (hinj heq)
  let τL : A ≃ₐ[L] A := { τ.toRingEquiv with commutes' := hfixL }
  refine ⟨τL.restrictNormal Ω', fun x => ?_⟩
  apply (algebraMap Ω' A).injective
  rw [AlgEquiv.restrictNormal_commutes]
  exact hτ x

end GlobalTheory.SepExt
