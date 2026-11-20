import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `S X₀ Xg X' e f W' jW jQ he hjQ hjW hcomm x hx`. Use `he` as an intermediate fact. Establish `hO : IsOpenImmersion (W'.ι ≫ f)`. Rewrite using `[← hcomm]`. Use `infer_instance`.

Take `⟨y, rfl⟩ : ∃ y : W'.toScheme, W'.ι y = x` from `⟨⟨x, hx⟩, rfl⟩`. Establish `h1 : Function.Surjective ((W'.ι ≫ f).stalkMap y)` using `Scheme.Hom.stalkMap_surjective (W'.ι ≫ f) y`. Use `(IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion W'.ι)).2 y` as an intermediate fact. Establish `hι : Function.Bijective (W'.ι.stalkMap y)` using `ConcreteCategory.bijective_of_isIso _`. Establish `key : Function.Surjective (f.stalkMap (W'.ι y))`.

Introduce `t`. Take `⟨s, hs⟩` from `h1 (W'.ι.stalkMap y t)`. Use `⟨s, hι.1 ?_⟩` and prove the remaining obligations. Rewrite `hs` using `[Scheme.Hom.stalkMap_comp]`. Conclude with `hs`.

Rewrite using `[Scheme.Hom.stalkMap_comp]`. Conclude with `key.comp (Scheme.Hom.stalkMap_surjective e (f (W'.ι y)))`.
-/
theorem stalkMap_comp_surjective_of_open_part :
    ∀ (S X₀ Xg X' : Scheme.{0}) (e : Xg ⟶ X₀) (f : X' ⟶ Xg) (W' : X'.Opens)
      (jW : W'.toScheme ⟶ S) (jQ : S ⟶ Xg), IsPreimmersion e → IsOpenImmersion jQ → IsIso jW →
      jW ≫ jQ = W'.ι ≫ f → ∀ x ∈ W', Function.Surjective ((f ≫ e).stalkMap x).hom := by
  intro S X₀ Xg X' e f W' jW jQ he hjQ hjW hcomm x hx
  have := he
  have hO : IsOpenImmersion (W'.ι ≫ f) := by
    rw [← hcomm]
    infer_instance
  obtain ⟨y, rfl⟩ : ∃ y : W'.toScheme, W'.ι y = x := ⟨⟨x, hx⟩, rfl⟩
  have h1 : Function.Surjective ((W'.ι ≫ f).stalkMap y) :=
    Scheme.Hom.stalkMap_surjective (W'.ι ≫ f) y
  have := (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion W'.ι)).2 y
  have hι : Function.Bijective (W'.ι.stalkMap y) := ConcreteCategory.bijective_of_isIso _
  have key : Function.Surjective (f.stalkMap (W'.ι y)) := by
    intro t
    obtain ⟨s, hs⟩ := h1 (W'.ι.stalkMap y t)
    refine ⟨s, hι.1 ?_⟩
    rw [Scheme.Hom.stalkMap_comp] at hs
    exact hs
  rw [Scheme.Hom.stalkMap_comp]
  exact key.comp (Scheme.Hom.stalkMap_surjective e (f (W'.ι y)))

end GlobalTheory.CompanionTheory.Ar.Flat
