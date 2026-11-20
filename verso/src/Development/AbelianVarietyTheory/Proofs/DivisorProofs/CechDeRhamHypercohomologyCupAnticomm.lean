import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

/- English proof (translation)
Introduce `R _ C _ F a b`. Take `⟨a, rfl⟩` from `Hyp1.mk_surjective F a`. Take `⟨b, rfl⟩` from `Hyp1.mk_surjective F b`. Rewrite using `[cupHyp_mk, cupHyp_mk, ← map_add]`. Use `Hyp2.mk_eq_zero.2 ⟨(fun T T' φ ↦ -(a.1.1 T T' φ * b.1.1 T T' φ), 0), ?_⟩` and prove the remaining obligations.

Use `Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_` and prove the remaining obligations. Simplify using `only [cechDeRhamTotalDifferentialOne_functionPart, Submodule.coe_add, Prod.fst_add, Pi.add_apply, coe_cupZZ, cupTot_apply, cechDeRhamTotalCocyclesOne.comp a, cechDeRhamTotalCocyclesOne.comp b, map_mul, map_neg]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [dTot1_a, Submodule.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply, coe_cupZZ, cupTot_a, map_neg, Derivation.leibniz, Pi.zero_apply, map_zero]`. Rewrite using `[cechDeRhamTotalCocyclesOne.conn a φ, cechDeRhamTotalCocyclesOne.conn b φ]`.

Use `module`. Simplify using `only [dTot1_η, Submodule.coe_add, Prod.snd_add, Pi.add_apply, coe_cupZZ, cupTot_η, Pi.zero_apply, map_zero]`. Rewrite using `[wedge_swap (a.1.2 T), neg_add_cancel]`.
-/
theorem cupHyp_add_cupHyp_swap : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    ∀ a b : Hyp1 F, cupHyp F a b + cupHyp F b a = 0 := by
  intro R _ C _ F a b
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F a
  obtain ⟨b, rfl⟩ := Hyp1.mk_surjective F b
  rw [cupHyp_mk, cupHyp_mk, ← map_add]
  refine Hyp2.mk_eq_zero.2 ⟨(fun T T' φ ↦ -(a.1.1 T T' φ * b.1.1 T T' φ), 0), ?_⟩
  refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_
  · simp only [cechDeRhamTotalDifferentialOne_functionPart, Submodule.coe_add, Prod.fst_add, Pi.add_apply, coe_cupZZ, cupTot_apply,
      cechDeRhamTotalCocyclesOne.comp a, cechDeRhamTotalCocyclesOne.comp b, map_mul, map_neg]
    ring
  · simp only [dTot1_a, Submodule.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply, coe_cupZZ,
      cupTot_a, map_neg, Derivation.leibniz, Pi.zero_apply, map_zero]
    rw [cechDeRhamTotalCocyclesOne.conn a φ, cechDeRhamTotalCocyclesOne.conn b φ]
    module
  · simp only [dTot1_η, Submodule.coe_add, Prod.snd_add, Pi.add_apply, coe_cupZZ, cupTot_η,
      Pi.zero_apply, map_zero]
    rw [wedge_swap (a.1.2 T), neg_add_cancel]

end GlobalTheory.AbCoh
