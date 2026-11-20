import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

/- English proof (translation)
Introduce `k G _ _ X _ S hS`. Establish `hf : Function.Injective S.f.hom` using `(Rep.mono_iff_injective _).1 hS.mono_f`. Establish `hg : Function.Surjective S.g.hom` using `(Rep.epi_iff_surjective _).1 hS.epi_g`. Establish `hex : LinearMap.range S.f.hom.toLinearMap = LinearMap.ker S.g.hom.toLinearMap` using `(hS.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker`. Establish `hfg : ∀ a, S.g.hom (S.f.hom a) = 0` using `fun a => by`.

Use `congrArg (fun φ => Rep.Hom.hom φ a) S.zero` as an intermediate fact. Conclude with `this`. Establish `hz : permCoef X S.f ≫ permCoef X S.g = 0`. Use extensionality with `x a y`. Express the relevant statement in the definitionally equal form `S.g.hom (S.f.hom (Finsupp.single x a y)) = 0`.

Conclude with `hfg _`. Use `⟨hz, ?_⟩` and prove the remaining obligations. Establish `hm : Mono (permCoef X S.f)`. Rewrite using `[Rep.mono_iff_injective]`. Conclude with `Finsupp.mapRange_injective _ (map_zero _) hf`.

Establish `he : Epi (permCoef X S.g)`. Rewrite using `[Rep.epi_iff_surjective]`. Conclude with `Finsupp.mapRange_surjective _ (map_zero _) hg`. Use `{ exact := ?_ }` and prove the remaining obligations. Rewrite using `[← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)), ShortComplex.moduleCat_exact_iff_range_eq_ker]`.

Express the relevant statement in the definitionally equal form `(Finsupp.mapRange.linearMap S.f.hom.toLinearMap : (X →₀ S.X₁) →ₗ[k] (X →₀ S.X₂)).range = (Finsupp.mapRange.linearMap S.g.hom.toLinearMap : (X →₀ S.X₂) →ₗ[k] (X →₀ S.X₃)).ker`. Rewrite using `[Finsupp.ker_mapRange, Finsupp.range_mapRange_linearMap _ (LinearMap.ker_eq_bot.2 hf), hex]`.
-/
theorem permCoef_shortExact : ∀ (k G : Type) [CommRing k] [Group G] (X : Type) [MulAction G X] (S : ShortComplex (Rep k G)), S.ShortExact → ∃ h : permCoef X S.f ≫ permCoef X S.g = 0, (ShortComplex.mk (permCoef X S.f) (permCoef X S.g) h).ShortExact := by
  intro k G _ _ X _ S hS
  have hf : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have hex : LinearMap.range S.f.hom.toLinearMap = LinearMap.ker S.g.hom.toLinearMap :=
    (hS.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
  have hfg : ∀ a, S.g.hom (S.f.hom a) = 0 := fun a => by
    have := congrArg (fun φ => Rep.Hom.hom φ a) S.zero
    exact this
  have hz : permCoef X S.f ≫ permCoef X S.g = 0 := by
    ext x a y
    change S.g.hom (S.f.hom (Finsupp.single x a y)) = 0
    exact hfg _
  refine ⟨hz, ?_⟩
  have hm : Mono (permCoef X S.f) := by
    rw [Rep.mono_iff_injective]
    exact Finsupp.mapRange_injective _ (map_zero _) hf
  have he : Epi (permCoef X S.g) := by
    rw [Rep.epi_iff_surjective]
    exact Finsupp.mapRange_surjective _ (map_zero _) hg
  refine { exact := ?_ }
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change (Finsupp.mapRange.linearMap S.f.hom.toLinearMap : (X →₀ S.X₁) →ₗ[k] (X →₀ S.X₂)).range =
    (Finsupp.mapRange.linearMap S.g.hom.toLinearMap : (X →₀ S.X₂) →ₗ[k] (X →₀ S.X₃)).ker
  rw [Finsupp.ker_mapRange, Finsupp.range_mapRange_linearMap _ (LinearMap.ker_eq_bot.2 hf), hex]

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.HomStab.permCoef_shortExact`.
-/
theorem _root_.GlobalTheory.T.permCoef_preserves_shortExact : ∀ (k G : Type) [CommRing k] [Group G] (X : Type) [MulAction G X] (S : ShortComplex (Rep k G)), S.ShortExact → ∃ h : permCoef X S.f ≫ permCoef X S.g = 0, (ShortComplex.mk (permCoef X S.f) (permCoef X S.g) h).ShortExact := by
  first
  | exact @GlobalTheory.HomStab.permCoef_shortExact
end
