import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.AbelianHodgeDeRham.Bridge

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR FubiniStudyChowHeightFormula₂.Hdr

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Free

/- English proof (translation)
Introduce `R _ A _ g hA hg`. Take `⟨⟨a1, a2, a3⟩, hw, ⟨f1, f2, f3⟩, ⟨o1, o2, -⟩, ⟨hcl, hinj, hsurj⟩, hbc⟩` from `H R A g hA hg`. Set `i` to `formEquiv A.hom hcl hinj`. Establish `hk : Hodge1 A.hom = LinearMap.ker (toHO1 A.hom)` using `(cechHodgeFiltration_eq_range A.hom).symm`. Set `q : (HH1 A.hom ⧸ Hodge1 A.hom) ≃ₗ[R] HO1 A.hom` to `(Submodule.quotEquivOfEq _ _ hk).trans ((toHO1 A.hom).quotKerEquivOfSurjective hsurj)`.

Use `⟨hw, ⟨⟨a1, a2⟩, a3⟩, ⟨hcl, hinj, ⟨⟨Module.Finite.equiv i, Module.Projective.of_equiv i⟩, fun p ↦ by rw [← Module.rankAtStalk_eq_of_equiv i, f3]⟩, Module.Finite.equiv q.symm, Module.Projective.of_equiv q.symm⟩, ⟨by rw [hk]; exact LinearMap.exact_subtype_ker_map _, hsurj⟩, fun R' _ …` and prove the remaining obligations. Take `⟨b1, ⟨e, he⟩, b3⟩` from `hbc R' X' s' φ h`. Use `⟨b1, ?_, b3⟩` and prove the remaining obligations. Take `⟨_, hA'⟩` from `exists_abelian A hA h`. Establish `hg' : SmoothOfRelativeDimension g (Over.mk s').hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h hg`.

Take `⟨-, -, -, -, ⟨hcl', hinj', -⟩, -⟩` from `H R' (Over.mk s') g hA' hg'`. Set `i'` to `formEquiv s' hcl' hinj'`. Use `⟨(LinearEquiv.baseChange R R' _ _ i.symm).trans (e.trans i'), fun c ↦ ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `i.surjective c`. Establish `k : ((LinearEquiv.baseChange R R' _ _ i.symm).trans (e.trans i')) (1 ⊗ₜ i c) = i' (e (1 ⊗ₜ c))`.

Simplify using the standard rewrite rules. Rewrite using `[k]`. Conclude with `IsPullForm.cl (ω := ⟨c, hcl ▸ trivial⟩) (ω' := ⟨e (1 ⊗ₜ c), hcl' ▸ trivial⟩) (he c)`.
-/
theorem page_of_hodge (H : GlobalTheory.Published.AbelianHodgeDeRham) : AbelianDeRhamPage := by
  intro R _ A _ g hA hg
  obtain ⟨⟨a1, a2, a3⟩, hw, ⟨f1, f2, f3⟩, ⟨o1, o2, -⟩, ⟨hcl, hinj, hsurj⟩, hbc⟩ := H R A g hA hg
  let i := formEquiv A.hom hcl hinj
  have hk : Hodge1 A.hom = LinearMap.ker (toHO1 A.hom) := (cechHodgeFiltration_eq_range A.hom).symm
  let q : (HH1 A.hom ⧸ Hodge1 A.hom) ≃ₗ[R] HO1 A.hom :=
    (Submodule.quotEquivOfEq _ _ hk).trans ((toHO1 A.hom).quotKerEquivOfSurjective hsurj)
  refine ⟨hw, ⟨⟨a1, a2⟩, a3⟩, ⟨hcl, hinj, ⟨⟨Module.Finite.equiv i, Module.Projective.of_equiv i⟩,
      fun p ↦ by rw [← Module.rankAtStalk_eq_of_equiv i, f3]⟩,
      Module.Finite.equiv q.symm, Module.Projective.of_equiv q.symm⟩,
    ⟨by rw [hk]; exact LinearMap.exact_subtype_ker_map _, hsurj⟩, fun R' _ _ X' s' φ h ↦ ?_⟩
  obtain ⟨b1, ⟨e, he⟩, b3⟩ := hbc R' X' s' φ h
  refine ⟨b1, ?_, b3⟩
  obtain ⟨_, hA'⟩ := exists_abelian A hA h
  have hg' : SmoothOfRelativeDimension g (Over.mk s').hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h hg
  obtain ⟨-, -, -, -, ⟨hcl', hinj', -⟩, -⟩ := H R' (Over.mk s') g hA' hg'
  let i' := formEquiv s' hcl' hinj'
  refine ⟨(LinearEquiv.baseChange R R' _ _ i.symm).trans (e.trans i'), fun c ↦ ?_⟩
  obtain ⟨c, rfl⟩ := i.surjective c
  have k : ((LinearEquiv.baseChange R R' _ _ i.symm).trans (e.trans i')) (1 ⊗ₜ i c) = i' (e (1 ⊗ₜ c)) := by
    simp
  rw [k]
  exact IsPullForm.cl (ω := ⟨c, hcl ▸ trivial⟩) (ω' := ⟨e (1 ⊗ₜ c), hcl' ▸ trivial⟩) (he c)

end MainStatements.Hodge.Free
