import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.QCoh GlobalTheory.VB GlobalTheory.MixedLocalChains

namespace GlobalTheory.MixedLocalChains

/- English proof (translation)
Establish `hi : IsIso ((Scheme.Modules.restrictFunctor U.ι).map ψ)` using `(NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) ψ).2 inferInstance`. Use `mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun a b e => ?_⟩` and prove the remaining obligations. Establish `hη` using `genericPoint_mem hx`. Establish `hle : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) ≤ W` using `U.ι.image_preimage_le W`. Establish `hη' : genericPoint X ∈ U.ι ''ᵁ (U.ι ⁻¹ᵁ W)` using `⟨⟨_, hU⟩, hη, rfl⟩`.

Establish `hinj : Function.Injective (ψ.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ W)))` using `(ConcreteCategory.bijective_of_isIso (((Scheme.Modules.restrictFunctor U.ι).map ψ).app (U.ι ⁻¹ᵁ W))).1`. Use `sub_eq_zero.1 (h W hη _ ?_)` and prove the remaining obligations. Establish `n` using `fun s => ConcreteCategory.congr_hom (ψ.mapPresheaf.naturality (homOfLE hle).op) s`. Establish `e' : G.presheaf.map (homOfLE hle).op a = G.presheaf.map (homOfLE hle).op b` using `hinj ((n a).trans ((congrArg _ e).trans (n b).symm))`. Rewrite using `[map_sub, sub_eq_zero, ← G.presheaf.germ_res_apply (homOfLE hle) _ hη' a, ← G.presheaf.germ_res_apply (homOfLE hle) _ hη' b, e']`.
-/
theorem mono_of_isIso_pullback_ι {X : Scheme.{0}} [IsIntegral X] {F G : X.Modules}
    (h : IsTorsionFree G) (ψ : G ⟶ F) (U : X.Opens) (hU : genericPoint X ∈ U)
    [IsIso ((Scheme.Modules.pullback U.ι).map ψ)] : Mono ψ := by
  have hi : IsIso ((Scheme.Modules.restrictFunctor U.ι).map ψ) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) ψ).2 inferInstance
  refine mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun a b e => ?_⟩
  have hη := genericPoint_mem hx
  have hle : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) ≤ W := U.ι.image_preimage_le W
  have hη' : genericPoint X ∈ U.ι ''ᵁ (U.ι ⁻¹ᵁ W) := ⟨⟨_, hU⟩, hη, rfl⟩
  have hinj : Function.Injective (ψ.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ W))) :=
    (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.restrictFunctor U.ι).map ψ).app (U.ι ⁻¹ᵁ W))).1
  refine sub_eq_zero.1 (h W hη _ ?_)
  have n := fun s => ConcreteCategory.congr_hom (ψ.mapPresheaf.naturality (homOfLE hle).op) s
  have e' : G.presheaf.map (homOfLE hle).op a = G.presheaf.map (homOfLE hle).op b :=
    hinj ((n a).trans ((congrArg _ e).trans (n b).symm))
  rw [map_sub, sub_eq_zero, ← G.presheaf.germ_res_apply (homOfLE hle) _ hη' a,
    ← G.presheaf.germ_res_apply (homOfLE hle) _ hη' b, e']

/- English proof (translation)
Introduce `_ _ _ _ B P` and use `have := P.iso mono_of_isIso_pullback_ι P.vb'.isTorsionFree P.ψ B.gen B.genericPoint_mem_gen`.
-/
theorem Pres.mono_ψ : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (B : GlobalTheory.Vert.Model O) (P : Pres B), Mono P.ψ := fun _ _ _ _ B P =>
  have := P.iso
  mono_of_isIso_pullback_ι P.vb'.isTorsionFree P.ψ B.gen B.genericPoint_mem_gen

end GlobalTheory.MixedLocalChains
