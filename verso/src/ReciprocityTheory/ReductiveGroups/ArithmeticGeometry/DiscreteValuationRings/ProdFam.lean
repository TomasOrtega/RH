import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

section FamPr

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D' D : DegPre R}

/- English proof (translation)
Use `haveI := pD.pw.hom i`. Establish `hc` using `pD.c_pr α' i`. Apply the tactic sequence `fin_cases a <;>`. Simplify using `[DegPre.famφB, ← Over.comp_left, padd, hc, IsMonHom.mul_hom, IsMonHom.one_hom]`. Apply the tactic sequence `all_goals first`.

Consider the case `(rw [← Over.comp_left]; congr 1;`. Simplify using `[CartesianMonoidalCategory.comp_lift_assoc, CartesianMonoidalCategory.comp_lift, hc, IsMonHom.mul_hom, CartesianMonoidalCategory.comp_toUnit_assoc])`. Consider the case `(congr 1; simp [CartesianMonoidalCategory.comp_lift_assoc, CartesianMonoidalCategory.comp_lift, hc, IsMonHom.mul_hom, CartesianMonoidalCategory.comp_toUnit_assoc])`.
-/
theorem famφB_pr (pD : IsPowDeg D' D j) (α' : D'.X) (i : Fin j) (a : Fin 4) :
    D'.famφB α' a ≫ (pD.pw.pr i).left = (pD.pw.pr i).left ≫ D.famφB (pD.xe α' i) a := by
  haveI := pD.pw.hom i
  have hc := pD.c_pr α' i
  fin_cases a <;>
    simp [DegPre.famφB, ← Over.comp_left, padd, hc, IsMonHom.mul_hom, IsMonHom.one_hom]
  all_goals
    first
    | (rw [← Over.comp_left]; congr 1;
        simp [CartesianMonoidalCategory.comp_lift_assoc, CartesianMonoidalCategory.comp_lift, hc,
          IsMonHom.mul_hom, CartesianMonoidalCategory.comp_toUnit_assoc])
    | (congr 1; simp [CartesianMonoidalCategory.comp_lift_assoc, CartesianMonoidalCategory.comp_lift, hc,
          IsMonHom.mul_hom, CartesianMonoidalCategory.comp_toUnit_assoc])

def boxFamB (pD : IsPowDeg D' D j) (k : ℕ) (f : Fin j → ∀ α : D.X, D.SecB k α) (α' : D'.X) : D'.SecB k α' :=
  secOfIso (u := LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k))
    (boxSecGen D.P.L (fun i => (pD.pw.pr i).left) (D'.famφB α') (DegPre.famε k) (fun i => (pD.pw.pr i).left)
      (fun i => D.famφB (pD.xe α' i)) (famφB_pr pD α') (fun i => f i (pD.xe α' i)))
    (linCombIso_isGen pD.w pD.w_gen _ _) (linComb_isLB _ D'.P.isLB _ _)
    (linComb_isLB _ (linComb_isLB _ D.P.isLB _ _) _ _)

/- English proof (translation)
Introduce `α'`. Use `⟨famφB_pr pD α', fun jN jM => ?_⟩` and prove the remaining obligations. Use `set V := LB.wchart (boxLB D.P.L pD.pw.pr) (D'.famφB α') jN ⊓ LB.wchart D'.P.L (D'.famφB α') jM with hVdef`. Establish `hVab : V ≤ LB.wchart D'.P.L (D'.famφB α') jM ⊓ LB.wchart (boxLB D.P.L pD.pw.pr) (D'.famφB α') jN` using `fun _ hy => ⟨hy.2, hy.1⟩`. Establish `hspec` using `congrArg (rs hVab) (secOfIso_spec (u := LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k)) (boxSecGen D.P.L (fun i => (pD.pw.pr i).left) (D'.famφB α') (DegPre.famε k) (fun i => (pD.pw.pr i).left) (fun i => D.famφB (pD.xe α' i)) (famφB_pr pD α') (fun i => f i (pD.xe α' i))) (linCom …`.

Use `erw [rs_rs] at hspec`. Establish `hspec2` using `hspec.trans (isoCand_rs (LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k)) (boxSecGen D.P.L (fun i => (pD.pw.pr i).left) (D'.famφB α') (DegPre.famε k) (fun i => (pD.pw.pr i).left) (fun i => D.famφB (pD.xe α' i)) (famφB_pr pD α') (fun i => f i (pD.xe α' i))) jM jN hVab)`. Establish `hVd : V ≤ (LB.div (LB.LinComb (boxLB D.P.L pD.pw.pr) (D'.famφB α') (DegPre.famε k)) (LB.LinComb D'.P.L (D'.famφB α') (DegPre.famε k))).U (jN, jM)` using `fun _ hy => ⟨hy.1, hy.2⟩`. Establish `hu : res hVd ((LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k)).s (jN, jM)) = @id (Γ(D'.P.A.left, V)ˣ) ((LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k)).s (jN, jM))` using `res_refl' _`. Establish `key` using `unit_cancel _ _ _ _ hspec2 hu`.

Use `key.trans ?_` and prove the remaining obligations. Simplify using `only [boxSecGen, boxSecGenF]`. Use `(map_prod ((D'.P.A.left.presheaf.map (homOfLE _).op).hom) _ _).trans (Finset.prod_congr rfl fun i _ => ?_)` and prove the remaining obligations. Conclude with `rs_rs _ _ _`.
-/
theorem isBoxFamB_boxFamB (pD : IsPowDeg D' D j) (k : ℕ) (f : Fin j → ∀ α : D.X, D.SecB k α) :
    IsBoxFamB pD k (boxFamB pD k f) f := by
  intro α'
  refine ⟨famφB_pr pD α', fun jN jM => ?_⟩
  set V := LB.wchart (boxLB D.P.L pD.pw.pr) (D'.famφB α') jN ⊓ LB.wchart D'.P.L (D'.famφB α') jM with hVdef
  have hVab : V ≤ LB.wchart D'.P.L (D'.famφB α') jM ⊓ LB.wchart (boxLB D.P.L pD.pw.pr) (D'.famφB α') jN :=
    fun _ hy => ⟨hy.2, hy.1⟩
  have hspec := congrArg (rs hVab) (secOfIso_spec (u := LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k))
    (boxSecGen D.P.L (fun i => (pD.pw.pr i).left) (D'.famφB α') (DegPre.famε k) (fun i => (pD.pw.pr i).left)
      (fun i => D.famφB (pD.xe α' i)) (famφB_pr pD α') (fun i => f i (pD.xe α' i)))
    (linCombIso_isGen pD.w pD.w_gen _ _) (linComb_isLB _ D'.P.isLB _ _)
    (linComb_isLB _ (linComb_isLB _ D.P.isLB _ _) _ _) jM jN)
  erw [rs_rs] at hspec
  have hspec2 := hspec.trans (isoCand_rs (LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k))
    (boxSecGen D.P.L (fun i => (pD.pw.pr i).left) (D'.famφB α') (DegPre.famε k) (fun i => (pD.pw.pr i).left)
      (fun i => D.famφB (pD.xe α' i)) (famφB_pr pD α') (fun i => f i (pD.xe α' i))) jM jN hVab)
  have hVd : V ≤ (LB.div (LB.LinComb (boxLB D.P.L pD.pw.pr) (D'.famφB α') (DegPre.famε k))
      (LB.LinComb D'.P.L (D'.famφB α') (DegPre.famε k))).U (jN, jM) := fun _ hy => ⟨hy.1, hy.2⟩
  have hu : res hVd ((LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k)).s (jN, jM)) =
      @id (Γ(D'.P.A.left, V)ˣ) ((LB.linCombIso pD.w (D'.famφB α') (DegPre.famε k)).s (jN, jM)) :=
    res_refl' _
  have key := unit_cancel _ _ _ _ hspec2 hu
  refine key.trans ?_
  simp only [boxSecGen, boxSecGenF]
  refine (map_prod ((D'.P.A.left.presheaf.map (homOfLE _).op).hom) _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  exact rs_rs _ _ _

end FamPr

end ReciprocityTheory.ChartRestriction.G.DVR
