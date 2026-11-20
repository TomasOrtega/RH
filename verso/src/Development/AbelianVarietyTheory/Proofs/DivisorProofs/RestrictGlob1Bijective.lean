import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ C _ C' _ F G hsep hglue`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `ω hω`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `T`. Use `hsep T (ω.1 T) fun t u ↦ ?_` and prove the remaining obligations. Establish `h1` using `congrArg (fun x : Glob1 (G ⋙ F) ↦ x.1 t) hω`. Establish `h2 : (pullGlob1 (CoefMap.restrict F G) ω).1 t = ω.1 (G.obj t)` using `cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _`. Rewrite using `[← ω.2 u, ← h2, h1]`.

Both sides reduce to the same expression. Introduce `ω'`. Establish `hc : ∀ (T : C), ∃ ω : Ω[F.obj T⁄R], ∀ t (u : T ⟶ G.obj t), p1 F u ω = ω'.1 t` using `fun T ↦ hglue T (fun t _ ↦ ω'.1 t) fun t t' u a ↦ ω'.2 a`. Use `choose ω hω using hc`. Establish `hglob : ω ∈ Glob1 F`.

Introduce `T T' φ`. Rewrite using `[← sub_eq_zero]`. Use `hsep T' _ fun t u ↦ ?_` and prove the remaining obligations. Rewrite using `[map_sub, ← oneFormsMapOfFunctorMorphism_comp, hω, hω, sub_self]`. Use `⟨⟨ω, hglob⟩, Subtype.ext (funext fun t ↦ ?_)⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `q1 (CoefMap.restrict F G) t (ω (G.obj t)) = ω'.1 t`. Rewrite using `[cechDeRhamCoefMapOneForms_restrictAlongFunctor, ← hω (G.obj t) t (𝟙 _), oneFormsMapOfFunctorMorphism_id]`.
-/
theorem restrict_glob1_bijective : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (ω : Ω[F.obj T⁄R]), (∀ t (u : T ⟶ G.obj t), p1 F u ω = 0) → ω = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → Ω[F.obj (G.obj t)⁄R]), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = p1 F (G.map a) (s t u)) → ∃ ω : Ω[F.obj T⁄R], ∀ t u, p1 F u ω = s t u) → Function.Bijective (pullGlob1 (CoefMap.restrict F G)) := by
  intro R _ C _ C' _ F G hsep hglue
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro ω hω
    apply Subtype.ext
    funext T
    refine hsep T (ω.1 T) fun t u ↦ ?_
    have h1 := congrArg (fun x : Glob1 (G ⋙ F) ↦ x.1 t) hω
    have h2 : (pullGlob1 (CoefMap.restrict F G) ω).1 t = ω.1 (G.obj t) := cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _
    rw [← ω.2 u, ← h2, h1]
    rfl
  · intro ω'
    have hc : ∀ (T : C), ∃ ω : Ω[F.obj T⁄R], ∀ t (u : T ⟶ G.obj t), p1 F u ω = ω'.1 t :=
      fun T ↦ hglue T (fun t _ ↦ ω'.1 t) fun t t' u a ↦ ω'.2 a
    choose ω hω using hc
    have hglob : ω ∈ Glob1 F := by
      intro T T' φ
      rw [← sub_eq_zero]
      refine hsep T' _ fun t u ↦ ?_
      rw [map_sub, ← oneFormsMapOfFunctorMorphism_comp, hω, hω, sub_self]
    refine ⟨⟨ω, hglob⟩, Subtype.ext (funext fun t ↦ ?_)⟩
    change q1 (CoefMap.restrict F G) t (ω (G.obj t)) = ω'.1 t
    rw [cechDeRhamCoefMapOneForms_restrictAlongFunctor, ← hω (G.obj t) t (𝟙 _), oneFormsMapOfFunctorMorphism_id]

end GlobalTheory
