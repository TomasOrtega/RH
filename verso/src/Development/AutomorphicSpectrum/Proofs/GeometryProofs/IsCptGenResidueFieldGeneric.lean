import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem injective_of_maximal_point {X : Scheme.{0}} {Ω : Type} [Field Ω] (p : X)
    [IsDomain (X.presheaf.stalk p)] (φ : X.presheaf.stalk p ⟶ CommRingCat.of Ω)
    (h : ∀ y : X, y ⤳ (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint Ω) →
      y = (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint Ω)) :
    Function.Injective φ.hom := by
  let z : PrimeSpectrum (X.presheaf.stalk p) := ⟨⊥, Ideal.isPrime_bot⟩
  let q : PrimeSpectrum (X.presheaf.stalk p) := PrimeSpectrum.comap φ.hom (IsLocalRing.closedPoint Ω)
  have hs : z ⤳ q := (PrimeSpectrum.le_iff_specializes z q).1 bot_le
  have hq : (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint Ω) = X.fromSpecStalk p q := rfl
  rw [hq] at h
  have h1 : X.fromSpecStalk p z = X.fromSpecStalk p q :=
    h _ (hs.map (X.fromSpecStalk p).continuous)
  have h2 : z = q := (X.fromSpecStalk p).isEmbedding.injective h1
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  have h3 : a ∈ q.asIdeal := by
    change φ.hom a ∈ (IsLocalRing.closedPoint Ω).asIdeal
    rw [ha]
    exact Ideal.zero_mem _
  rw [← h2] at h3
  exact h3

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isCptGen_of_maximal_of_surjective {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : ∀ y : X, y ⤳ genPt ξ → y = genPt ξ)
    (hs : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) : IsCptGen ξ := by
  refine ⟨⟨?_, hs⟩, fun p => ?_⟩
  · have := hX (ξ (IsLocalRing.closedPoint Ω))
    refine injective_of_maximal_point _ (Scheme.stalkClosedPointTo ξ) ?_
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    exact h
  · obtain ⟨p, hp⟩ := p
    have := hX p
    have hp' : ξ (IsLocalRing.closedPoint Ω) ⤳ p := hp
    refine injective_of_maximal_point p
      (X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ) ?_
    have e : Spec.map (X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ) ≫
        X.fromSpecStalk p = ξ := by
      rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    rw [e]
    exact h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isCptGen_of_maximal : ∀ (X : Scheme.{0}), (∀ x : X, IsDomain (X.presheaf.stalk x)) → ∀ x : X,
    (∀ y : X, y ⤳ x → y = x) → IsCptGen (Ω := X.residueField x) (X.fromSpecResidueField x) := by
  intro X hX x h
  have e : genPt (Ω := X.residueField x) (X.fromSpecResidueField x) = x :=
    X.fromSpecResidueField_apply x _
  refine isCptGen_of_maximal_of_surjective hX _ (by rw [e]; exact h) ?_
  unfold Scheme.stalkClosedPointTo
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso _).hom).2.comp
    ((X.fromSpecResidueField x).stalkMap_surjective _)

end GlobalTheory.CompanionTheory.Ar
