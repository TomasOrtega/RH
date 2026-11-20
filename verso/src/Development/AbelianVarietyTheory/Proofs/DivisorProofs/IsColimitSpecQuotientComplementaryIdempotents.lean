import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open Limits

/- English proof (translation)
Establish `he' : e' = 1 - e` using `by rw [← hs]; ring`. Establish `hee : e * e' = 0` using `by rw [he', mul_sub, _root_.mul_one, he.eq, sub_self]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Simplify using `only [RingHom.prod_apply, Prod.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx`. Take `⟨⟨a, rfl⟩, ⟨b, hb⟩⟩` from `hx`. Establish `h1 : a * e * e' = 0` using `by rw [_root_.mul_assoc, hee, mul_zero]`. Establish `h2 : a * e * e = 0`. Rewrite using `[← hb, _root_.mul_assoc, mul_comm e' e, hee, mul_zero]`.

Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨x, y⟩`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Use `⟨a * e' + b * e, ?_⟩` and prove the remaining obligations.

Simplify using `only [RingHom.prod_apply, Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Conclude with `⟨b - a, by rw [he']; ring⟩`. Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton']`.

Conclude with `⟨a - b, by rw [he']; ring⟩`.
-/
theorem specQuotIdemCoprod_bij (R : Type) [CommRing R] (e e' : R) (he : IsIdempotentElem e)
    (hs : e + e' = 1) :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span {e})).prod
      (Ideal.Quotient.mk (Ideal.span {e'}))) := by
  have he' : e' = 1 - e := by rw [← hs]; ring
  have hee : e * e' = 0 := by rw [he', mul_sub, _root_.mul_one, he.eq, sub_self]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    simp only [RingHom.prod_apply, Prod.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton'] at hx
    obtain ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩ := hx
    have h1 : a * e * e' = 0 := by rw [_root_.mul_assoc, hee, mul_zero]
    have h2 : a * e * e = 0 := by
      rw [← hb, _root_.mul_assoc, mul_comm e' e, hee, mul_zero]
    calc a * e = a * e * (e + e') := by rw [hs, _root_.mul_one]
      _ = 0 := by rw [mul_add, h1, h2, add_zero]
  · rintro ⟨x, y⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨a * e' + b * e, ?_⟩
    simp only [RingHom.prod_apply, Prod.mk.injEq]
    constructor
    · rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      exact ⟨b - a, by rw [he']; ring⟩
    · rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      exact ⟨a - b, by rw [he']; ring⟩

/- English proof (translation)
Introduce `R _ e e' he hs`. Set `A` to `R ⧸ Ideal.span {e}`. Set `B` to `R ⧸ Ideal.span {e'}`. Set `φ : R →+* A × B` to `(Ideal.Quotient.mk (Ideal.span {e})).prod (Ideal.Quotient.mk (Ideal.span {e'}))`. Establish `hφ : Function.Bijective φ` using `specQuotIdemCoprod_bij R e e' he hs`.

Set `ψ : R ≃+* A × B` to `RingEquiv.ofBijective φ hφ`. Set `g : Spec (CommRingCat.of A) ⨿ Spec (CommRingCat.of B) ⟶ Sp R` to `coprodSpec A B ≫ Spec.map (CommRingCat.ofHom φ)`. Use `haveI : IsIso (Spec.map (CommRingCat.ofHom φ)) := by`. Establish `: IsIso (CommRingCat.ofHom φ)`. Express the relevant statement in the definitionally equal form `IsIso (RingEquiv.toCommRingCatIso ψ).hom`.

Use `infer_instance`. Use `infer_instance`. Use `haveI : IsIso g := by dsimp only [g]; infer_instance`. Set `i` to `asIso g`. Use `⟨IsColimit.ofIsoColimit (coprodIsCoprod (Spec (CommRingCat.of A)) (Spec (CommRingCat.of B))) (Cocone.ext i ?_)⟩` and prove the remaining obligations.

Introduce and unpack `⟨⟨⟩⟩`. Simplify using `only [i, asIso_hom, g] show coprod.inl ≫ coprodSpec A B ≫ _ = spMap _`. Rewrite using `[coprodSpec_inl_assoc, ← Spec.map_comp]`. Both sides reduce to the same expression. Simplify using `only [i, asIso_hom, g] show coprod.inr ≫ coprodSpec A B ≫ _ = spMap _`.

Rewrite using `[coprodSpec_inr_assoc, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem specQuotIdemCoprod : ∀ (R : Type) [CommRing R] (e e' : R), IsIdempotentElem e → e + e' = 1 → Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk (spMap (Ideal.Quotient.mk (Ideal.span {e}))) (spMap (Ideal.Quotient.mk (Ideal.span {e'}))))) := by
  intro R _ e e' he hs
  let A := R ⧸ Ideal.span {e}
  let B := R ⧸ Ideal.span {e'}
  let φ : R →+* A × B := (Ideal.Quotient.mk (Ideal.span {e})).prod
      (Ideal.Quotient.mk (Ideal.span {e'}))
  have hφ : Function.Bijective φ := specQuotIdemCoprod_bij R e e' he hs
  let ψ : R ≃+* A × B := RingEquiv.ofBijective φ hφ
  let g : Spec (CommRingCat.of A) ⨿ Spec (CommRingCat.of B) ⟶ Sp R :=
    coprodSpec A B ≫ Spec.map (CommRingCat.ofHom φ)
  haveI : IsIso (Spec.map (CommRingCat.ofHom φ)) := by
    have : IsIso (CommRingCat.ofHom φ) := by
      change IsIso (RingEquiv.toCommRingCatIso ψ).hom
      infer_instance
    infer_instance
  haveI : IsIso g := by dsimp only [g]; infer_instance
  let i := asIso g
  refine ⟨IsColimit.ofIsoColimit (coprodIsCoprod (Spec (CommRingCat.of A)) (Spec (CommRingCat.of B)))
    (Cocone.ext i ?_)⟩
  rintro ⟨⟨⟩⟩
  · simp only [i, asIso_hom, g]
    show coprod.inl ≫ coprodSpec A B ≫ _ = spMap _
    rw [coprodSpec_inl_assoc, ← Spec.map_comp]
    rfl
  · simp only [i, asIso_hom, g]
    show coprod.inr ≫ coprodSpec A B ≫ _ = spMap _
    rw [coprodSpec_inr_assoc, ← Spec.map_comp]
    rfl

end GlobalTheory
