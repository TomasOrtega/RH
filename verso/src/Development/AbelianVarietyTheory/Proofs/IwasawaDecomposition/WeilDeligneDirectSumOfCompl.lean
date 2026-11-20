import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

namespace GlobalTheory.WeilDeligne.PrimDecomp

/- English proof (translation)
Rewrite using `[WD.lpSum_mk]`. Use `symm`. Apply `WD.sound` to reduce the goal to its premises. Use `⟨Submodule.prodEquivOfIsCompl S T hST, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `σ ⟨x, y⟩`.

Simplify using `only [WDRep.sum_ρ, LinearMap.prodMap_apply, Submodule.coe_prodEquivOfIsCompl', map_add, restrict_ρ_apply]`. Introduce and unpack `⟨x, y⟩`. Simplify using `only [WDRep.sum_N, LinearMap.prodMap_apply, Submodule.coe_prodEquivOfIsCompl', map_add, restrict_N_apply]`.
-/
theorem wd_mk_eq_lpSum_restrict_of_isCompl {E Ω : Type} [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (S T : Submodule ℂ V) (hS : IsSubWD a S) (hT : IsSubWD a T)
    (hST : IsCompl S T) :
    WD.mk a = (WD.mk (restrict a S hS)).lpSum (WD.mk (restrict a T hT)) := by
  rw [WD.lpSum_mk]
  symm
  apply WD.sound
  refine ⟨Submodule.prodEquivOfIsCompl S T hST, ?_, ?_⟩
  · rintro σ ⟨x, y⟩
    simp only [WDRep.sum_ρ, LinearMap.prodMap_apply, Submodule.coe_prodEquivOfIsCompl',
      map_add, restrict_ρ_apply]
  · rintro ⟨x, y⟩
    simp only [WDRep.sum_N, LinearMap.prodMap_apply, Submodule.coe_prodEquivOfIsCompl',
      map_add, restrict_N_apply]

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ A w h V _ _ _ a S T hS hT hST` and use `wd_mk_eq_lpSum_restrict_of_isCompl A w h V a S T hS hT hST`.
-/
theorem sumiso : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (S T : Submodule ℂ V) (hS : IsSubWD a S) (hT : IsSubWD a T), IsCompl S T → WD.mk a = (WD.mk (restrict a S hS)).lpSum (WD.mk (restrict a T hT)) :=
  fun _ _ _ _ _ _ _ A w h V _ _ _ a S T hS hT hST =>
    wd_mk_eq_lpSum_restrict_of_isCompl A w h V a S T hS hT hST

end GlobalTheory.WeilDeligne.PrimDecomp
