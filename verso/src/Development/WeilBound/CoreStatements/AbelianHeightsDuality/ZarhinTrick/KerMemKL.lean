import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamC

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar.Z2

/- English proof (translation)
Establish `hx0 : lam (cls L hL) (fst T ((Over.pullback s).obj A) ≫ x) (snd T ((Over.pullback s).obj A)) = 0`. Rewrite using `[lam_comm, lam_cL_pt s hD.isLB l L hL e, ← toBase_map, Category.assoc, hx, MonObj.comp_one, toBase_one]`. Conclude with `evc_one_right hD.isLB hD.zero _`. Establish `hD' : (Out.translDiff ((Over.pullback s).obj A) L x).IsLB` using `LB.isLB_linComb hL _ _`. Introduce `p`.

Take `⟨V, hV, hc⟩` from `exists_pull_eq_zero (GlobalTheory.CechPic.pull x.left (cls L hL) - GlobalTheory.CechPic.pull (1 : T ⟶ (Over.pullback s).obj A).left (cls L hL)) p`. Use `⟨V, hV, (cls_eq_zero_iff (pull_isLB hD' _)).1 ?_⟩` and prove the remaining obligations. Establish `e₁` using `pull_translDiff hL x hD' (fst T _) (snd T _)`. Rewrite `e₁` using `[lift_fst_snd, Over.id_left, pull_id]`. Establish `e₂ : cls _ hD' = GlobalTheory.CechPic.pull (fst T ((Over.pullback s).obj A)).left (GlobalTheory.CechPic.pull x.left (cls L hL) - GlobalTheory.CechPic.pull (1 : T ⟶ (Over.pullback s).obj A).left (cls L hL))`.

Rewrite using `[e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one, ← sub_eq_zero, ← hx0, lam]`. Normalize the expressions using the abelian group laws. Rewrite using `[cls_pull hD', e₂, ← pull_comp]`. Conclude with `pull_eq_zero_of_mem V (((fst T _).left ⁻¹ᵁ V).ι ≫ (fst T _).left) (fun z ↦ z.2) hc`.
-/
theorem ker_memKL {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (l : A ⟶ B) [IsMonHom l] {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) [IsCommMonObj ((Over.pullback s).obj A)]
    (L : LB ((Over.pullback s).obj A).left)
    (hL : L.IsLB) (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    {T : Over (Sp Ω)} (x : T ⟶ (Over.pullback s).obj A) (hx : x ≫ (Over.pullback s).map l = 1) :
    GlobalTheory.MemKL ((Over.pullback s).obj A) L x := by
  have hx0 : lam (cls L hL) (fst T ((Over.pullback s).obj A) ≫ x) (snd T ((Over.pullback s).obj A)) = 0 := by
    rw [lam_comm, lam_cL_pt s hD.isLB l L hL e, ← toBase_map, Category.assoc, hx, MonObj.comp_one, toBase_one]
    exact evc_one_right hD.isLB hD.zero _
  have hD' : (Out.translDiff ((Over.pullback s).obj A) L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
    (GlobalTheory.CechPic.pull x.left (cls L hL) - GlobalTheory.CechPic.pull (1 : T ⟶ (Over.pullback s).obj A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD' _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD' (fst T _) (snd T _)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD' = GlobalTheory.CechPic.pull (fst T ((Over.pullback s).obj A)).left
      (GlobalTheory.CechPic.pull x.left (cls L hL) - GlobalTheory.CechPic.pull (1 : T ⟶ (Over.pullback s).obj A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hx0, lam]
    abel
  rw [cls_pull hD', e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T _).left ⁻¹ᵁ V).ι ≫ (fst T _).left) (fun z ↦ z.2) hc

end PositivityTheory.PrwZar.Z2
