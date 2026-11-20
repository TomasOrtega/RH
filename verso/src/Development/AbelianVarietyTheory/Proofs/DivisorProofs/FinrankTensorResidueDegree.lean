import Mathlib
open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.ResidueTensorRank

/- English proof (translation)
Use `letI := hK.toField`. Use `letI := hA.toField`. Use `algebraize [a.hom, b.hom, i.hom, j.hom, (a ≫ i).hom]`. Use `haveI : IsScalarTower K A P := .of_algebraMap_eq' rfl`. Use `haveI : IsScalarTower K B P := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)`.

Establish `hp : Algebra.IsPushout K A B P` using `CommRingCat.isPushout_iff_isPushout.mp h`. Conclude with `hp.out.finrank_eq`.
-/
theorem finrank_pushout_inl {K A B P : CommRingCat.{0}} (hK : IsField K) (hA : IsField A) (a : K ⟶ A) (b : K ⟶ B)
    (i : A ⟶ P) (j : B ⟶ P) (h : IsPushout a b i j) :
    @Module.finrank A P _ _ i.hom.toModule = @Module.finrank K B _ _ b.hom.toModule := by
  letI := hK.toField
  letI := hA.toField
  algebraize [a.hom, b.hom, i.hom, j.hom, (a ≫ i).hom]
  haveI : IsScalarTower K A P := .of_algebraMap_eq' rfl
  haveI : IsScalarTower K B P := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have hp : Algebra.IsPushout K A B P := CommRingCat.isPushout_iff_isPushout.mp h
  exact hp.out.finrank_eq

/- English proof (translation)
Introduce `X Y S f g T`. Take `⟨x, y, s, hx, hy⟩` from `T`. Substitute `hy` using the available equality. Use `finrank_pushout_inl (Field.toIsField _) (Field.toIsField _) _ _ _ _ (IsPushout.of_hasPushout ((S.residueFieldCongr hx).inv ≫ f.residueFieldMap x) ((S.residueFieldCongr (rfl : g y = g y)).inv ≫ g.residueFieldMap y))` as an intermediate fact. Use `this.trans ?_` and prove the remaining obligations.

Simplify using `only [Scheme.residueFieldCongr_refl, Iso.refl_inv, Category.id_comp]`. Both sides reduce to the same expression.
-/
theorem finrank_tensorInl : ∀ {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (T : Scheme.Pullback.Triplet f g), @Module.finrank (X.residueField T.x) T.tensor _ _ T.tensorInl.hom.toModule = g.residueDegree T.y := by
  intro X Y S f g T
  obtain ⟨x, y, s, hx, hy⟩ := T
  subst hy
  have := finrank_pushout_inl (Field.toIsField _) (Field.toIsField _) _ _ _ _ (IsPushout.of_hasPushout ((S.residueFieldCongr hx).inv ≫ f.residueFieldMap x) ((S.residueFieldCongr (rfl : g y = g y)).inv ≫ g.residueFieldMap y))
  refine this.trans ?_
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_inv, Category.id_comp]
  rfl

end GlobalTheory.ResidueTensorRank
