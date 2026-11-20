import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ C _ C' _ F G hSep hGlue κ hκ θ' hθ'`. Establish `key : ∀ T : C, ∃ ω : Ω[F.obj T⁄R], ∀ t (u : T ⟶ G.obj t), p1 F u ω = θ' t - κ T (G.obj t) u`. Introduce `T`. Use `hGlue T (fun t u ↦ θ' t - κ T (G.obj t) u) ?_` and prove the remaining obligations. Introduce `t t' u a`.

Simplify using `only [map_sub]`. Rewrite using `[hκ u (G.map a), hθ' a]`. Normalize the expressions using the abelian group laws. Use `choose θ hθ using key`. Use `⟨θ, fun T T' φ ↦ ?_⟩` and prove the remaining obligations.

Establish `h0 : κ T T' φ - θ T' + p1 F φ (θ T) = 0`. Use `hSep T' _ (fun t u ↦ ?_)` and prove the remaining obligations. Establish `e1` using `hκ φ u`. Establish `e2` using `hθ T' t u`. Establish `e3` using `hθ T t (φ ≫ u)`.

Rewrite `e3` using `[oneFormsMapOfFunctorMorphism_comp]`. Simplify using `only [map_add, map_sub, e2, e3]`. Rewrite using `[e1]`. Normalize the expressions using the abelian group laws. Rewrite using `[← sub_eq_zero]`.

Rewrite using `[← h0]`. Normalize the expressions using the abelian group laws.
-/
theorem cocycle_one_forms_coboundary_of_restrict : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (ω : Ω[F.obj T⁄R]), (∀ t (u : T ⟶ G.obj t), p1 F u ω = 0) → ω = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → Ω[F.obj (G.obj t)⁄R]), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = p1 F (G.map a) (s t u)) → ∃ ω : Ω[F.obj T⁄R], ∀ t u, p1 F u ω = s t u) → ∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) → ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T) := by
  intro R _ C _ C' _ F G hSep hGlue κ hκ θ' hθ'
  have key : ∀ T : C, ∃ ω : Ω[F.obj T⁄R], ∀ t (u : T ⟶ G.obj t),
      p1 F u ω = θ' t - κ T (G.obj t) u := by
    intro T
    refine hGlue T (fun t u ↦ θ' t - κ T (G.obj t) u) ?_
    intro t t' u a
    simp only [map_sub]
    rw [hκ u (G.map a), hθ' a]
    abel
  choose θ hθ using key
  refine ⟨θ, fun T T' φ ↦ ?_⟩
  have h0 : κ T T' φ - θ T' + p1 F φ (θ T) = 0 := by
    refine hSep T' _ (fun t u ↦ ?_)
    have e1 := hκ φ u
    have e2 := hθ T' t u
    have e3 := hθ T t (φ ≫ u)
    rw [oneFormsMapOfFunctorMorphism_comp] at e3
    simp only [map_add, map_sub, e2, e3]
    rw [e1]
    abel
  rw [← sub_eq_zero]
  rw [← h0]
  abel

end GlobalTheory
