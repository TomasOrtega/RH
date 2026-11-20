import Mathlib

namespace GlobalTheory

/- English proof (translation)
Use `letI : Algebra L F := (g.comp φ.symm.toRingHom).toAlgebra`. Set `g' : M →ₐ[L] F` to `IsAlgClosed.lift`. Use `⟨g'.toRingHom, RingHom.ext fun x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `g' (algebraMap L _ (φ x)) = g x`. Rewrite using `[g'.commutes]`.

Express the relevant statement in the definitionally equal form `g (φ.symm (φ x)) = g x`. Rewrite using `[φ.symm_apply_apply]`.
-/
theorem exists_extend_of_ringEquiv_of_isAlgebraic {K L M F : Type} [Field K] [Field L] [Field M] [Field F]
    [IsAlgClosed F] [Algebra L M] [Algebra.IsAlgebraic L M] (φ : K ≃+* L) (g : K →+* F) :
    ∃ g' : M →+* F, g'.comp ((algebraMap L M).comp φ.toRingHom) = g := by
  letI : Algebra L F := (g.comp φ.symm.toRingHom).toAlgebra
  let g' : M →ₐ[L] F := IsAlgClosed.lift
  refine ⟨g'.toRingHom, RingHom.ext fun x => ?_⟩
  change g' (algebraMap L _ (φ x)) = g x
  rw [g'.commutes]
  change g (φ.symm (φ x)) = g x
  rw [φ.symm_apply_apply]

/- English proof (translation)
Introduce `R _ _ _ _ _ s`. Establish `: CharZero (FractionRing R)` using `IsFractionRing.charZero_of_isFractionRing R`. Set `L : IntermediateField (FractionRing R) (AlgebraicClosure (FractionRing R))` to `IntermediateField.adjoin (FractionRing R) {s}`. Establish `: FiniteDimensional (FractionRing R) L` using `IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)`. Establish `: Algebra.IsSeparable (FractionRing R) L` using `inferInstance`.

Establish `hfin : Module.Finite R (integralClosure R L)` using `IsIntegralClosure.finite R (FractionRing R) L (integralClosure R L)`. Establish `hfr : IsFractionRing (integralClosure R L) L` using `integralClosure.isFractionRing_of_finite_extension (FractionRing R) L`. Set `φ : FractionRing (integralClosure R L) ≃+* L` to `(FractionRing.algEquiv (integralClosure R L) L).toRingEquiv`. Establish `hφ : ∀ x : integralClosure R L, φ (algebraMap (integralClosure R L) _ x) = algebraMap (integralClosure R L) L x` using `fun x => (FractionRing.algEquiv (integralClosure R L) L).commutes x`. Use `⟨integralClosure R L, inferInstance, inferInstance, algebraMap R _, φ.symm.toRingHom.comp (algebraMap (FractionRing R) L), (algebraMap L (AlgebraicClosure (FractionRing R))).comp φ.toRingHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `a b hab`. Establish `h1 : algebraMap R L a = algebraMap R L b`. Rewrite using `[IsScalarTower.algebraMap_apply R (integralClosure R L) L, IsScalarTower.algebraMap_apply R (integralClosure R L) L b, hab]`. Rewrite `h1` using `[IsScalarTower.algebraMap_apply R (FractionRing R) L, IsScalarTower.algebraMap_apply R (FractionRing R) L b]`. Conclude with `IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) L).injective h1)`.

Conclude with `RingHom.finite_algebraMap.2 hfin`. Conclude with `(isIntegrallyClosed_iff_isIntegrallyClosedIn L).2 inferInstance`. Introduce `r`. Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[hφ, ← IsScalarTower.algebraMap_apply R (integralClosure R L) L, IsScalarTower.algebraMap_apply R (FractionRing R) L]`.

Conclude with `φ.apply_symm_apply _`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap L _ (φ (φ.symm (algebraMap (FractionRing R) L x))) = _`. Rewrite using `[φ.apply_symm_apply, ← IsScalarTower.algebraMap_apply]`. Use `⟨φ.symm ⟨s, IntermediateField.mem_adjoin_simple_self _ s⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `algebraMap L _ (φ (φ.symm _)) = _`. Rewrite using `[φ.apply_symm_apply]`. Both sides reduce to the same expression. Introduce `F _ _ g`. Establish `: Algebra.IsAlgebraic L (AlgebraicClosure (FractionRing R))` using `Algebra.IsAlgebraic.tower_top (K := FractionRing R) L`.

Conclude with `exists_extend_of_ringEquiv_of_isAlgebraic φ g`.
-/
theorem exists_finite_normal_adjoin_algebraic :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R]
      (s : AlgebraicClosure (FractionRing R)),
      ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R →+* R₂)
        (h' : FractionRing R →+* FractionRing R₂)
        (e : FractionRing R₂ →+* AlgebraicClosure (FractionRing R)),
        Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧
        (∀ r, h' (algebraMap R _ r) = algebraMap R₂ _ (h r)) ∧ e.comp h' = algebraMap _ _ ∧
        (∃ s₂, e s₂ = s) ∧
        ∀ (F : Type) [Field F] [IsAlgClosed F] (g : FractionRing R₂ →+* F),
          ∃ g' : AlgebraicClosure (FractionRing R) →+* F, g'.comp e = g := by
  intro R _ _ _ _ _ s
  have : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  let L : IntermediateField (FractionRing R) (AlgebraicClosure (FractionRing R)) :=
    IntermediateField.adjoin (FractionRing R) {s}
  have : FiniteDimensional (FractionRing R) L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)
  have : Algebra.IsSeparable (FractionRing R) L := inferInstance
  have hfin : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R (FractionRing R) L (integralClosure R L)
  have hfr : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing R) L
  let φ : FractionRing (integralClosure R L) ≃+* L :=
    (FractionRing.algEquiv (integralClosure R L) L).toRingEquiv
  have hφ : ∀ x : integralClosure R L,
      φ (algebraMap (integralClosure R L) _ x) = algebraMap (integralClosure R L) L x :=
    fun x => (FractionRing.algEquiv (integralClosure R L) L).commutes x
  refine ⟨integralClosure R L, inferInstance, inferInstance, algebraMap R _,
    φ.symm.toRingHom.comp (algebraMap (FractionRing R) L),
    (algebraMap L (AlgebraicClosure (FractionRing R))).comp φ.toRingHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : algebraMap R L a = algebraMap R L b := by
      rw [IsScalarTower.algebraMap_apply R (integralClosure R L) L,
        IsScalarTower.algebraMap_apply R (integralClosure R L) L b, hab]
    rw [IsScalarTower.algebraMap_apply R (FractionRing R) L,
      IsScalarTower.algebraMap_apply R (FractionRing R) L b] at h1
    exact IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) L).injective h1)
  · exact RingHom.finite_algebraMap.2 hfin
  · exact (isIntegrallyClosed_iff_isIntegrallyClosedIn L).2 inferInstance
  · intro r
    apply φ.injective
    rw [hφ, ← IsScalarTower.algebraMap_apply R (integralClosure R L) L,
      IsScalarTower.algebraMap_apply R (FractionRing R) L]
    exact φ.apply_symm_apply _
  · refine RingHom.ext fun x => ?_
    change algebraMap L _ (φ (φ.symm (algebraMap (FractionRing R) L x))) = _
    rw [φ.apply_symm_apply, ← IsScalarTower.algebraMap_apply]
  · refine ⟨φ.symm ⟨s, IntermediateField.mem_adjoin_simple_self _ s⟩, ?_⟩
    change algebraMap L _ (φ (φ.symm _)) = _
    rw [φ.apply_symm_apply]
    rfl
  · intro F _ _ g
    have : Algebra.IsAlgebraic L (AlgebraicClosure (FractionRing R)) :=
      Algebra.IsAlgebraic.tower_top (K := FractionRing R) L
    exact exists_extend_of_ringEquiv_of_isAlgebraic φ g

end GlobalTheory
