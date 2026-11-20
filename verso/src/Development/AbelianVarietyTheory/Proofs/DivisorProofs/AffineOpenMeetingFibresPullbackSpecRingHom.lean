import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem affine_preimage_pullback_meets_fibres {R R' : Type} [CommRing R] [CommRing R'] (a : R →+* R')
    (A : Over (Sp R)) (W : A.left.Opens) : IsAffineOpen W →
    (∀ t ∈ Set.range (spMap a), ∃ x ∈ W, A.hom x = t) →
    ∃ V : ((Over.pullback (spMap a)).obj A).left.Opens, IsAffineOpen V ∧
      ∀ s : Sp R', ∃ x ∈ V, ((Over.pullback (spMap a)).obj A).hom x = s := by
  intro hW hfib
  haveI : IsAffineHom (pullback.fst A.hom (spMap a)) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  refine ⟨(pullback.fst A.hom (spMap a)) ⁻¹ᵁ W, hW.preimage _, ?_⟩
  intro s
  obtain ⟨x, hxW, hx⟩ := hfib (spMap a s) ⟨s, rfl⟩
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := A.hom) (g := spMap a) x s hx
  exact ⟨z, by show (pullback.fst A.hom (spMap a)) z ∈ W; rw [hz1]; exact hxW, hz2⟩

end GlobalTheory
