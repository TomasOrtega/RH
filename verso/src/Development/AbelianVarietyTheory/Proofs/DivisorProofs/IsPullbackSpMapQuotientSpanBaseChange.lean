import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.QuotBaseChange

/- English proof (translation)
Use `⟨⟨by ext a; exact (congr($hρ a)).symm⟩, ⟨Limits.PushoutCocone.IsColimit.mk _ (fun s => CommRingCat.ofHom (Ideal.Quotient.lift (Ideal.span {π f}) s.inl.hom ?_)) ?_ ?_ ?_⟩⟩` and prove the remaining obligations. Introduce `b hb`. Establish `e : ∀ a, s.inl.hom (π a) = s.inr.hom (Ideal.Quotient.mk _ a)` using `fun a => congr($(s.condition) a)`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hb`. Rewrite using `[map_mul, e, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self f), map_zero, mul_zero]`.

Introduce `s`. Use extensionality with `b`. Both sides reduce to the same expression. Introduce `s`. Use extensionality with `a`.

Establish `e : s.inl.hom (π a) = s.inr.hom (Ideal.Quotient.mk _ a)` using `congr($(s.condition) a)`. Establish `e2 : ρ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (π a)` using `congr($hρ a)`. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]`. Rewrite using `[e2, Ideal.Quotient.lift_mk, e]`. Introduce `s m h₁ _`.

Use extensionality with `b`. Establish `e : m.hom (Ideal.Quotient.mk _ b) = s.inl.hom b` using `congr($h₁ b)`. Conclude with `e`.
-/
theorem isPushout_quot_span (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (f : R)
    (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f})
    (hρ : ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π) :
    IsPushout (CommRingCat.ofHom π) (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {π f}))) (CommRingCat.ofHom ρ) := by
  refine ⟨⟨by ext a; exact (congr($hρ a)).symm⟩, ⟨Limits.PushoutCocone.IsColimit.mk _
    (fun s => CommRingCat.ofHom (Ideal.Quotient.lift (Ideal.span {π f}) s.inl.hom ?_)) ?_ ?_ ?_⟩⟩
  · intro b hb
    have e : ∀ a, s.inl.hom (π a) = s.inr.hom (Ideal.Quotient.mk _ a) := fun a => congr($(s.condition) a)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    rw [map_mul, e, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self f), map_zero, mul_zero]
  · intro s
    ext b
    rfl
  · intro s
    ext a
    have e : s.inl.hom (π a) = s.inr.hom (Ideal.Quotient.mk _ a) := congr($(s.condition) a)
    have e2 : ρ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (π a) := congr($hρ a)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [e2, Ideal.Quotient.lift_mk, e]
  · intro s m h₁ _
    ext b
    have e : m.hom (Ideal.Quotient.mk _ b) = s.inl.hom b := congr($h₁ b)
    exact e

/- English proof (translation)
Introduce `R R₀ _ _ π f ρ hρ`. Conclude with `isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quot_span R R₀ π f ρ hρ)`.
-/
theorem isPullback_spMap_quot : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (f : R) (ρ : R ⧸ Ideal.span {f} →+* R₀ ⧸ Ideal.span {π f}), ρ.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp π → IsPullback (spMap (Ideal.Quotient.mk (Ideal.span {π f}))) (spMap ρ) (spMap π) (spMap (Ideal.Quotient.mk (Ideal.span {f}))) := by
  intro R R₀ _ _ π f ρ hρ
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quot_span R R₀ π f ρ hρ)

end GlobalTheory.QuotBaseChange
