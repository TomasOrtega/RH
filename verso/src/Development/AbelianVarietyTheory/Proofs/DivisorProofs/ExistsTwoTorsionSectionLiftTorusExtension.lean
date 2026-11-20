import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsZeroOfRed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TorusLift

open GlobalTheory.UU GlobalTheory.FormalPoint

section Lift

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)

/- English proof (translation)
The claim follows from `RedOnto.exists_coords U e g (thick R I e) (𝟙 _) ((Category.id_comp _).trans (Category.comp_id _).symm)`.
-/
theorem exists_coords (g : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))) (e : ℕ) :
    ∃ y : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left,
      RedOnto.Coords U e g (thick R I e) y :=
  RedOnto.exists_coords U e g (thick R I e) (𝟙 _) ((Category.id_comp _).trans (Category.comp_id _).symm)

variable [IsLocalRing R]

variable {U} in

/- English proof (translation)
Use `choose y hy using exists_coords U g`. Use `Over.OverMorphism.ext (hom_ext_of_isHausdorff I fun e => ?_)` and prove the remaining obligations. Conclude with `(RedOnto.comp_fstG_eq h (hy e)).symm.trans (RedOnto.comp_fstG_eq h' (hy e))`.
-/
theorem red_unique [IsHausdorff I R] {g : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))}
    {x x' : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G} (h : U.Red x g) (h' : U.Red x' g) : x = x' := by
  choose y hy using exists_coords U g
  refine Over.OverMorphism.ext (hom_ext_of_isHausdorff I fun e => ?_)
  exact (RedOnto.comp_fstG_eq h (hy e)).symm.trans (RedOnto.comp_fstG_eq h' (hy e))

/- English proof (translation)
Use `choose y hy using exists_coords U g`. Establish `hf : IsAdicFamily I fun e => y e ≫ (fstG I e G).left` using `fun e => by`. Establish `h₁` using `(hy (e + 1)).comp (adicLevelMap I (Nat.le_succ (e + 1)))`. Establish `h₂ : adicLevelMap I (Nat.le_succ (e + 1)) ≫ thick R I (e + 1) = thick R I e` using `adicLevelMap_ι _ _`. Establish `h₃ : RedOnto.Coords U (e + 1) g (thick R I e) (adicLevelMap I (Nat.le_succ (e + 1)) ≫ y (e + 1))` using `h₂ ▸ h₁`.

Establish `h₄ : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left` using `(pullback.lift_fst _ _ _).trans (Category.comp_id _)`. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I (e + 1) G).left) (h₃.unique (hy e).succ)).trans ((Category.assoc _ _ _).trans (congrArg _ h₄)))`. Take `⟨x, ⟨hx₁, hx₂⟩, -⟩` from `existsUnique_over_of_isAdicFamily (I := I) (𝟙 _) G.hom hf fun e => by`. Establish `h₁ : (fstG I e G).left ≫ G.hom = (U.gt e).pG.left ≫ D.P.A.hom` using `(Over.w (fstG I e G)).trans (Over.w (U.gt e).pG).symm`. Conclude with `(Category.assoc _ _ _).trans ((congrArg _ h₁).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ D.P.A.hom) (hy e).1).trans ((Category.assoc _ _ _).trans (congrArg _ (Over.w g.b))))))`.

Use `⟨Over.homMk x hx₁, fun e Z r xe hxe => ?_⟩` and prove the remaining obligations. Establish `hr : r = (xe ≫ (thickObj R I e G).hom) ≫ thick R I e`. Use `congrArg (· ≫ G.hom) hxe` as an intermediate fact. Simplify using `only [Category.assoc, Over.homMk_left, hx₁] at this`. Rewrite using `[← Category.comp_id r]`.

Use `this.symm.trans ?_` and prove the remaining obligations. Rewrite using `[Over.w (fstG I e G)]`. Both sides reduce to the same expression. Establish `hxe' : xe = (xe ≫ (thickObj R I e G).hom) ≫ y e`. Rewrite using `[← cancel_mono (fstG I e G).left, Category.assoc, ← hx₂ e, hxe]`.

Simplify using `only [Over.homMk_left]`. Rewrite using `[hr, Category.assoc]`. Use `(hy e).comp (xe ≫ (thickObj R I e G).hom)` as an intermediate fact. Rewrite `this` using `[← hr, ← hxe']`. Conclude with `this`.
-/
theorem exists_red [IsAdicComplete I R] (g : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R))))) :
    ∃ x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G, U.Red x g := by
  choose y hy using exists_coords U g
  have hf : IsAdicFamily I fun e => y e ≫ (fstG I e G).left := fun e => by
    have h₁ := (hy (e + 1)).comp (adicLevelMap I (Nat.le_succ (e + 1)))
    have h₂ : adicLevelMap I (Nat.le_succ (e + 1)) ≫ thick R I (e + 1) = thick R I e := adicLevelMap_ι _ _
    have h₃ : RedOnto.Coords U (e + 1) g (thick R I e) (adicLevelMap I (Nat.le_succ (e + 1)) ≫ y (e + 1)) :=
      h₂ ▸ h₁
    have h₄ : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I (e + 1) G).left)
      (h₃.unique (hy e).succ)).trans ((Category.assoc _ _ _).trans (congrArg _ h₄)))
  obtain ⟨x, ⟨hx₁, hx₂⟩, -⟩ := existsUnique_over_of_isAdicFamily (I := I) (𝟙 _) G.hom hf fun e => by
    have h₁ : (fstG I e G).left ≫ G.hom = (U.gt e).pG.left ≫ D.P.A.hom :=
      (Over.w (fstG I e G)).trans (Over.w (U.gt e).pG).symm
    exact (Category.assoc _ _ _).trans ((congrArg _ h₁).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ D.P.A.hom) (hy e).1).trans ((Category.assoc _ _ _).trans (congrArg _ (Over.w g.b))))))
  refine ⟨Over.homMk x hx₁, fun e Z r xe hxe => ?_⟩
  have hr : r = (xe ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    have := congrArg (· ≫ G.hom) hxe
    simp only [Category.assoc, Over.homMk_left, hx₁] at this
    rw [← Category.comp_id r]
    refine this.symm.trans ?_
    rw [Over.w (fstG I e G)]
    rfl
  have hxe' : xe = (xe ≫ (thickObj R I e G).hom) ≫ y e := by
    rw [← cancel_mono (fstG I e G).left, Category.assoc, ← hx₂ e, hxe]
    simp only [Over.homMk_left]
    rw [hr, Category.assoc]
  have := (hy e).comp (xe ≫ (thickObj R I e G).hom)
  rw [← hr, ← hxe'] at this
  exact this

end Lift

/- English proof (translation)
Introduce `R _ _ _ hR D A G _ _ hS U g hg`. Take `⟨z, hz, hgz⟩` from `hg`. Establish `: IsAdicComplete (maximalIdeal R) R` using `hR.1.2.2.2`. Take `⟨w, hw⟩` from `U.ext`. Set `U'` to `GlobalTheory.ValueForm.toPreU U.toUnifPre GlobalTheory.globalFns_holds hS w hw`.

Take `⟨a, ha⟩` from `exists_red U' g`. Use `⟨a, ?_, fun e ae _ hae => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_two]`. Conclude with `red_unique (RedAdd.red_mul GlobalTheory.globalFns_holds ha ha hgz) (RedAdd.red_one U' hz)`. Take `⟨h₁, h₂⟩` from `ha e _ (thick R (maximalIdeal R) e) ae hae`.

Use `⟨h₁, fun χ => corr_of_val D.toPre.P.isLB fun y J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp]`. Conclude with `h₂ χ y J hJ`.
-/
theorem exists_sec_sq_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∃ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 ∧ (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) := by
  intro R _ _ _ hR D A G _ _ hS U g hg
  obtain ⟨z, hz, hgz⟩ := hg
  have : IsAdicComplete (maximalIdeal R) R := hR.1.2.2.2
  obtain ⟨w, hw⟩ := U.ext
  let U' := GlobalTheory.ValueForm.toPreU U.toUnifPre GlobalTheory.globalFns_holds hS w hw
  obtain ⟨a, ha⟩ := exists_red U' g
  refine ⟨a, ?_, fun e ae _ hae => ?_⟩
  · rw [pow_two]
    exact red_unique (RedAdd.red_mul GlobalTheory.globalFns_holds ha ha hgz) (RedAdd.red_one U' hz)
  · obtain ⟨h₁, h₂⟩ := ha e _ (thick R (maximalIdeal R) e) ae hae
    refine ⟨h₁, fun χ => corr_of_val D.toPre.P.isLB fun y J hJ => ?_⟩
    rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp]
    exact h₂ χ y J hJ

end GlobalTheory.TorusLift
