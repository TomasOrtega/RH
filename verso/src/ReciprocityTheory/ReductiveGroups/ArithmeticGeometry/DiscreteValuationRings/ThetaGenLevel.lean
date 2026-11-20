import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenThick

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma resTop_scal {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens)
    (r : R) : resTop W (scal p r) = toW p W r := rfl

/- English proof (translation)
Use `choose g hg using fun j => exists_div p ha hJ (M.U j) (s.f j) (h0 j)`. Use `⟨⟨g, fun i j => ?_⟩, hg⟩` and prove the remaining obligations. Apply `sub_eq_zero.1` to reduce the goal to its premises. Apply `toW_mul_eq_zero p _ ha` to reduce the goal to its premises. Establish `c` using `s.compat i j`.

Rewrite `c` using `[hg i, hg j, map_mul, map_mul, toW_res, toW_res]`. Rewrite using `[mul_sub, sub_eq_zero, c]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sec_div {R : Type} [CommRing R] [IsDomain R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) [Flat p]
    {M : LB Y} (s : LB.Sec M) {a : R} (ha : a ≠ 0) {J : Ideal R} (hJ : J ≤ Ideal.span {a})
    (h0 : ∀ j, (pullback.fst p (tq J)).app _ (s.f j) = 0) :
    ∃ g : LB.Sec M, ∀ j, s.f j = toW p _ a * g.f j := by
  choose g hg using fun j => exists_div p ha hJ (M.U j) (s.f j) (h0 j)
  refine ⟨⟨g, fun i j => ?_⟩, hg⟩
  apply sub_eq_zero.1
  apply toW_mul_eq_zero p _ ha
  have c := s.compat i j
  rw [hg i, hg j, map_mul, map_mul, toW_res, toW_res] at c
  rw [mul_sub, sub_eq_zero, c]
  ring

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

/- English proof (translation)
Unfold `thickMap fstG pullback.map`. Simplify using `only [Over.homMk_left]`. Use `erw [pullback.lift_fst]`. Apply the tactic sequence `try simp`.
-/
lemma thickMap_fst (e : ℕ) : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left := by
  unfold thickMap fstG pullback.map
  simp only [Over.homMk_left]
  erw [pullback.lift_fst]
  try simp

/- English proof (translation)
The claim follows from `(Over.w g.pG).trans (Over.w (fstG I e G)).symm`.
-/
lemma pG_struct {e : ℕ} (g : GtCoord I D.toPre e G) :
    g.pG.left ≫ D.toPre.P.A.hom = (fstG I e G).left ≫ G.hom :=
  (Over.w g.pG).trans (Over.w (fstG I e G)).symm

end ReciprocityTheory.ChartRestriction.G.DVR.TG

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

/- English proof (translation)
Substitute `hf` using the available equality. Use `first`. Consider the case `exact hx`. Consider the case `(rw [Scheme.comp_app]; exact hx)`. Consider the case `(simp only [Scheme.comp_app, CommRingCat.comp_apply]; exact hx)`.
-/
lemma app_eq_zero_of_comp {X Y Z : Scheme.{0}} {f : X ⟶ Z} {g : X ⟶ Y} {h : Y ⟶ Z} (hf : g ≫ h = f)
    (W : Z.Opens) (x : Γ(Z, W)) (hx : g.app (h ⁻¹ᵁ W) (h.app W x) = 0) : f.app W x = 0 := by
  subst hf
  first
  | exact hx
  | (rw [Scheme.comp_app]; exact hx)
  | (simp only [Scheme.comp_app, CommRingCat.comp_apply]; exact hx)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def thickO (e : ℕ) : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶
    (Over.map (thick R I (e + 1))).obj (thickObj R I (e + 1) G) :=
  Over.homMk (thickMap R I e G) (by
    show thickMap R I e G ≫ pullback.snd G.hom (thick R I (e + 1)) ≫ thick R I (e + 1) =
      pullback.snd G.hom (thick R I e) ≫ thick R I e
    rw [thickMap, pullback.lift_snd_assoc, Category.assoc, thickTrans_comp])

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (U.gt_q e)`.
-/
lemma thickO_pG (U : UnifPre I D A G) (e : ℕ) : thickO e ≫ (U.gt (e + 1)).pG = (U.gt e).pG :=
  Over.OverMorphism.ext (U.gt_q e)

/- English proof (translation)
Use `WeightPf.Oφ_comp (thickO (G := G) (I := I) e) (U.gt (e + 1)).pG α k` as an intermediate fact. Rewrite `this` using `[thickO_pG]`. Conclude with `this`.
-/
lemma Oφ_thick (U : UnifPre I D A G) (e : ℕ) (α : D.toPre.X) (k : Fin 4) :
    thickMap R I e G ≫ D.toPre.Oφ (U.gt (e + 1)).pG α k = D.toPre.Oφ (U.gt e).pG α k := by
  have := WeightPf.Oφ_comp (thickO (G := G) (I := I) e) (U.gt (e + 1)).pG α k
  rw [thickO_pG] at this
  exact this

end ReciprocityTheory.ChartRestriction.G.DVR.TG
