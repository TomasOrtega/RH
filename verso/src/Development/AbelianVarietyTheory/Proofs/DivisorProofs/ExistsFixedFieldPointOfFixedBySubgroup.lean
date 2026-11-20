import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbVarRed

/- English proof (translation)
Take `⟨E, hE1, hE2, -⟩` from `GlobalTheory.SS.exists_fieldOfValues A.left Ω x.left`. Establish `hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω)`. Rewrite using `[← Spec.map_id]`. Use `congr 1`. Establish `hfix : ∀ c ∈ E, ∀ σ ∈ H, σ c = c`.

Introduce `c hc σ hσ`. Establish `h1 : spMap (σ : Ω →+* Ω) ≫ x.left = spMap (RingHom.id Ω) ≫ x.left`. Rewrite using `[hid, Category.id_comp]`. Conclude with `congrArg CommaMorphism.left (hx σ hσ)`. Conclude with `(hE1 _ _).1 h1 c hc`.

Use `(hE2 (IntermediateField.fixedField H) (algebraMap (IntermediateField.fixedField H) Ω)).1 ?_` and prove the remaining obligations. Introduce `c hc`. Conclude with `⟨⟨c, fun σ => hfix c hc σ σ.2⟩, rfl⟩`.
-/
theorem exists_fixedField_point (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω))
    (A : Over (Sp K)) (_ : LocallyOfFiniteType A.hom) (x : ptOver K Ω ⟶ A)
    (hx : ∀ σ ∈ H, specAut σ ≫ x = x) :
    ∃ y : Sp (IntermediateField.fixedField H) ⟶ A.left,
      spMap (algebraMap (IntermediateField.fixedField H) Ω) ≫ y = x.left := by
  obtain ⟨E, hE1, hE2, -⟩ := GlobalTheory.SS.exists_fieldOfValues A.left Ω x.left
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by
    rw [← Spec.map_id]
    congr 1
  have hfix : ∀ c ∈ E, ∀ σ ∈ H, σ c = c := by
    intro c hc σ hσ
    have h1 : spMap (σ : Ω →+* Ω) ≫ x.left = spMap (RingHom.id Ω) ≫ x.left := by
      rw [hid, Category.id_comp]
      exact congrArg CommaMorphism.left (hx σ hσ)
    exact (hE1 _ _).1 h1 c hc
  refine (hE2 (IntermediateField.fixedField H) (algebraMap (IntermediateField.fixedField H) Ω)).1 ?_
  intro c hc
  exact ⟨⟨c, fun σ => hfix c hc σ σ.2⟩, rfl⟩

end GlobalTheory.Published.AbVarRed
