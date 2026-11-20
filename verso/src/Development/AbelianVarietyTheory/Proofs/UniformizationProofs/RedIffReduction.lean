import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.RedOnto

open GlobalTheory.FormalPoint

section Level

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)
  {T : Over (Spec (CommRingCat.of R))}

def Coords (e : ℕ) (g : GtPt D T) {Z : Scheme.{0}} (r : Z ⟶ T.left)
    (y : Z ⟶ (thickObj R I e G).left) : Prop :=
  y ≫ (U.gt e).pG.left = r ≫ g.b.left ∧
    ∀ (χ : D.X) (z : Z) (J), Good D.P.L z J → val ((U.gt e).t χ) y z J = val (g.s χ) r z J

/- English proof (translation)
Unfold `PreU.Red Coords`. Conclude with `⟨fun h e Z r y hy => h e Z r y hy, fun h e Z r y hy => h e Z r y hy⟩`.
-/
theorem red_iff (x : T ⟶ G) (g : GtPt D T) :
    U.Red x g ↔ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T.left) (y : Z ⟶ (thickObj R I e G).left),
      y ≫ (fstG I e G).left = r ≫ x.left → Coords U e g r y := by
  unfold PreU.Red Coords
  exact ⟨fun h e Z r y hy => h e Z r y hy, fun h e Z r y hy => h e Z r y hy⟩

variable {U}

/- English proof (translation)
Unfold `Coords at h ⊢`. Take `⟨h1, h2⟩` from `h`. Use `⟨by rw [Category.assoc, h1, Category.assoc], fun χ w J hJ => ?_⟩` and prove the remaining obligations. Establish `hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ ((U.gt e).t χ) y) (LB.pullGen D.P.L _ _ (g.s χ) r)` using `corr_of_val D.P.isLB fun z J' hJ' => by`. Rewrite using `[val_pull hJ', val_pull hJ', Category.id_comp, Category.id_comp]`.

Conclude with `h2 χ z J' hJ'`. Establish `hk` using `val_corr hJ hc k`. Rewrite `hk` using `[val_pull hJ, val_pull hJ]`. Then use the resulting hypothesis.
-/
theorem Coords.comp {e : ℕ} {g : GtPt D T} {Z W : Scheme.{0}} {r : Z ⟶ T.left}
    {y : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) (k : W ⟶ Z) :
    Coords U e g (k ≫ r) (k ≫ y) := by
  unfold Coords at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [Category.assoc, h1, Category.assoc], fun χ w J hJ => ?_⟩

  have hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ ((U.gt e).t χ) y) (LB.pullGen D.P.L _ _ (g.s χ) r) :=
    corr_of_val D.P.isLB fun z J' hJ' => by
      rw [val_pull hJ', val_pull hJ', Category.id_comp, Category.id_comp]
      exact h2 χ z J' hJ'
  have hk := val_corr hJ hc k
  rwa [val_pull hJ, val_pull hJ] at hk

/- English proof (translation)
Unfold `Coords at h h'`. Conclude with `GlobalTheory.TorusCoord.ext_of_val (U.gt e) y y' (h.1.trans h'.1.symm) fun χ w J hJ => (h.2 χ w J hJ).trans (h'.2 χ w J hJ).symm`.
-/
theorem Coords.unique {e : ℕ} {g : GtPt D T} {Z : Scheme.{0}} {r : Z ⟶ T.left}
    {y y' : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) (h' : Coords U e g r y') : y = y' := by
  unfold Coords at h h'
  exact GlobalTheory.TorusCoord.ext_of_val (U.gt e) y y' (h.1.trans h'.1.symm)
    fun χ w J hJ => (h.2 χ w J hJ).trans (h'.2 χ w J hJ).symm

variable (U) in

/- English proof (translation)
Take `⟨x, hx1, hx2⟩` from `GlobalTheory.FormalPoint.exists_point (U.gt e) g (Z := Over.mk σ) (Over.homMk r h.symm)`. Use `⟨x, ?_⟩` and prove the remaining obligations. Unfold `Coords`. Use `⟨hx1, fun χ z J hJ => ?_⟩` and prove the remaining obligations. Establish `hv` using `hx2 χ Z (𝟙 Z) z J hJ`.

Rewrite `hv` using `[Category.id_comp, Category.id_comp]`. Conclude with `hv`.
-/
theorem exists_coords (e : ℕ) (g : GtPt D T) {Z : Scheme.{0}} (r : Z ⟶ T.left)
    (σ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (h : σ ≫ thick R I e = r ≫ T.hom) :
    ∃ y, Coords U e g r y := by
  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.FormalPoint.exists_point (U.gt e) g (Z := Over.mk σ)
    (Over.homMk r h.symm)
  refine ⟨x, ?_⟩
  unfold Coords
  refine ⟨hx1, fun χ z J hJ => ?_⟩
  have hv := hx2 χ Z (𝟙 Z) z J hJ
  rw [Category.id_comp, Category.id_comp] at hv
  exact hv

/- English proof (translation)
Unfold `Coords at h ⊢`. Take `⟨h1, h2⟩` from `h`. Use `⟨by rw [Category.assoc, U.gt_q e]; exact h1, fun χ z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[← val_pull hJ ((U.gt (e + 1)).t χ) (thickMap R I e G) y, val_corr hJ (U.gt_t e χ) y]`. Conclude with `h2 χ z J hJ`.
-/
theorem Coords.succ {e : ℕ} {g : GtPt D T} {Z : Scheme.{0}} {r : Z ⟶ T.left}
    {y : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) :
    Coords U (e + 1) g r (y ≫ thickMap R I e G) := by
  unfold Coords at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [Category.assoc, U.gt_q e]; exact h1, fun χ z J hJ => ?_⟩
  rw [← val_pull hJ ((U.gt (e + 1)).t χ) (thickMap R I e G) y, val_corr hJ (U.gt_t e χ) y]
  exact h2 χ z J hJ

/- English proof (translation)
Take `⟨h1, -⟩` from `h`. Establish `e1 : g.b.left ≫ D.P.A.hom = T.hom` using `Over.w g.b`. Establish `e2 : (U.gt e).pG.left ≫ D.P.A.hom = (thickObj R I e G).hom ≫ thick R I e` using `Over.w (U.gt e).pG`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem comp_hom_eq_of_coords {e : ℕ} {g : GtPt D T} {Z : Scheme.{0}} {r : Z ⟶ T.left}
    {y : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) :
    r ≫ T.hom = y ≫ (thickObj R I e G).hom ≫ thick R I e := by
  obtain ⟨h1, -⟩ := h
  have e1 : g.b.left ≫ D.P.A.hom = T.hom := Over.w g.b
  have e2 : (U.gt e).pG.left ≫ D.P.A.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (U.gt e).pG
  calc r ≫ T.hom = (r ≫ g.b.left) ≫ D.P.A.hom := by rw [Category.assoc, e1]
    _ = (y ≫ (U.gt e).pG.left) ≫ D.P.A.hom := by rw [h1]
    _ = y ≫ (thickObj R I e G).hom ≫ thick R I e := by rw [Category.assoc, e2]

/- English proof (translation)
Establish `hb` using `comp_hom_eq_of_coords h`. Establish `ex : x.left ≫ G.hom = T.hom` using `Over.w x`. Take `⟨a, ha⟩` from `GlobalTheory.FormalPoint.exists_lift_fstG (Z := Over.mk (y ≫ (thickObj R I e G).hom)) (Over.homMk (r ≫ x.left) (by show (r ≫ x.left) ≫ G.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e`. Rewrite using `[Category.assoc, ex, hb, Category.assoc]))`. Establish `ha' : a.left ≫ (fstG I e G).left = r ≫ x.left` using `congrArg CommaMorphism.left ha`.

Establish `hc : Coords U e g r a.left` using `hx e Z r a.left ha'`. Rewrite using `[← Coords.unique hc h]`. Conclude with `ha'`.
-/
theorem comp_fstG_eq {g : GtPt D T} {x : T ⟶ G} (hx : U.Red x g) {e : ℕ} {Z : Scheme.{0}}
    {r : Z ⟶ T.left} {y : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) :
    y ≫ (fstG I e G).left = r ≫ x.left := by
  have hb := comp_hom_eq_of_coords h
  have ex : x.left ≫ G.hom = T.hom := Over.w x

  obtain ⟨a, ha⟩ := GlobalTheory.FormalPoint.exists_lift_fstG (Z := Over.mk (y ≫ (thickObj R I e G).hom))
    (Over.homMk (r ≫ x.left) (by
      show (r ≫ x.left) ≫ G.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e
      rw [Category.assoc, ex, hb, Category.assoc]))
  have ha' : a.left ≫ (fstG I e G).left = r ≫ x.left := congrArg CommaMorphism.left ha
  have hc : Coords U e g r a.left := hx e Z r a.left ha'
  rw [← Coords.unique hc h]
  exact ha'

end Level

section Complete

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {S : Type} [CommRing S] {φ : R →+* S} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx e`. Conclude with `hx e _ _ _ (GlobalTheory.FormalPoint.reduction_fstG I x e)`. Introduce `h e Z r xe hxe`. Establish `ex : x.left ≫ G.hom = spMap φ` using `Over.w x`.

Establish `ef : (fstG I e G).left ≫ G.hom = (thickObj R I e G).hom ≫ thick R I e` using `Over.w (fstG I e G)`. Establish `hs : r ≫ spMap φ = (xe ≫ (thickObj R I e G).hom) ≫ thick R I e`. Rewrite using `[← ex, ← Category.assoc, ← hxe]`. Simplify using `only [Category.assoc, ef]`. Take `⟨l, hl⟩` from `GlobalTheory.FormalPoint.exists_factor_level I φ r _ hs`.

Establish `hc` using `Coords.comp (h e) l`. Establish `hred : l ≫ GlobalTheory.FormalPoint.reduction I x e = xe`. Rewrite using `[← cancel_mono (fstG I e G).left, Category.assoc, GlobalTheory.FormalPoint.reduction_fstG, ← Category.assoc, hl, hxe]`. Rewrite `hc` using `[hl, hred]`. Conclude with `hc`.
-/
theorem red_iff_reduction (g : GtPt D (Over.mk (spMap φ))) (x : Over.mk (spMap φ) ⟶ G) :
    U.Red x g ↔ ∀ e, Coords U e g (adicLevelι (I.map φ) (e + 1)) (reduction I x e) := by
  constructor
  · intro hx e
    exact hx e _ _ _ (GlobalTheory.FormalPoint.reduction_fstG I x e)
  · intro h e Z r xe hxe
    have ex : x.left ≫ G.hom = spMap φ := Over.w x
    have ef : (fstG I e G).left ≫ G.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (fstG I e G)
    have hs : r ≫ spMap φ = (xe ≫ (thickObj R I e G).hom) ≫ thick R I e := by
      rw [← ex, ← Category.assoc, ← hxe]
      simp only [Category.assoc, ef]

    obtain ⟨l, hl⟩ := GlobalTheory.FormalPoint.exists_factor_level I φ r _ hs
    have hc := Coords.comp (h e) l
    have hred : l ≫ GlobalTheory.FormalPoint.reduction I x e = xe := by
      rw [← cancel_mono (fstG I e G).left, Category.assoc, GlobalTheory.FormalPoint.reduction_fstG, ← Category.assoc,
        hl, hxe]
    rw [hl, hred] at hc
    exact hc

variable [IsLocalRing S]

variable {U} in

/- English proof (translation)
Establish `hr` using `(red_iff_reduction U g x).1 h`. Establish `hr'` using `(red_iff_reduction U g x').1 h'`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `GlobalTheory.hom_ext_of_isHausdorff (I.map φ)` to reduce the goal to its premises. Introduce `n`.

Rewrite using `[← GlobalTheory.FormalPoint.reduction_fstG I x n, ← GlobalTheory.FormalPoint.reduction_fstG I x' n, Coords.unique (hr n) (hr' n)]`.
-/
theorem red_unique [IsHausdorff (I.map φ) S] {g : GtPt D (Over.mk (spMap φ))}
    {x x' : Over.mk (spMap φ) ⟶ G} (h : U.Red x g) (h' : U.Red x' g) : x = x' := by
  have hr := (red_iff_reduction U g x).1 h
  have hr' := (red_iff_reduction U g x').1 h'
  apply Over.OverMorphism.ext
  apply GlobalTheory.hom_ext_of_isHausdorff (I.map φ)
  intro n
  rw [← GlobalTheory.FormalPoint.reduction_fstG I x n, ← GlobalTheory.FormalPoint.reduction_fstG I x' n, Coords.unique (hr n) (hr' n)]

/- English proof (translation)
Establish `hy : ∀ e, ∃ y, Coords U e g (adicLevelι (I.map φ) (e + 1)) y` using `fun e => exists_coords U e g (adicLevelι (I.map φ) (e + 1)) (GlobalTheory.FormalPoint.levelMap I φ e) (GlobalTheory.FormalPoint.levelMap_thick I φ e)`. Use `choose y hy using hy`. Establish `htf : ∀ n, thickMap R I n G ≫ (fstG I (n + 1) G).left = (fstG I n G).left`. Introduce `n`. Unfold `thickMap fstG`.

Simplify using `only [pullback.map, Category.comp_id]`. Conclude with `pullback.lift_fst _ _ _`. Establish `hcomp : ∀ n, GlobalTheory.adicLevelMap (I.map φ) (Nat.le_succ (n + 1)) ≫ y (n + 1) = y n ≫ thickMap R I n G`. Introduce `n`. Use `Coords.unique ?_ (Coords.succ (hy n))` and prove the remaining obligations.

Establish `hk` using `Coords.comp (hy (n + 1)) (GlobalTheory.adicLevelMap (I.map φ) (Nat.le_succ (n + 1)))`. Rewrite `hk` using `[GlobalTheory.adicLevelMap_ι]`. Then use the resulting hypothesis. Establish `hf : GlobalTheory.IsAdicFamily (I.map φ) (fun n => y n ≫ (fstG I n G).left)`. Introduce `n`. Use `show GlobalTheory.adicLevelMap (I.map φ) (Nat.le_succ (n + 1)) ≫ y (n + 1) ≫ (fstG I (n + 1) G).left = y n ≫ (fstG I n G).left`.

Rewrite using `[← Category.assoc, hcomp n, Category.assoc, htf n]`. Establish `hs : ∀ n, (y n ≫ (fstG I n G).left) ≫ G.hom = adicLevelι (I.map φ) (n + 1) ≫ spMap φ`. Introduce `n`. Establish `ef : (fstG I n G).left ≫ G.hom = (thickObj R I n G).hom ≫ thick R I n` using `Over.w (fstG I n G)`. Rewrite using `[Category.assoc, ef]`.

Conclude with `(comp_hom_eq_of_coords (hy n)).symm`. Take `⟨x₀, ⟨hx₀, hxn⟩, -⟩` from `GlobalTheory.existsUnique_over_of_isAdicFamily (spMap φ) G.hom hf hs`. Establish `hred : U.Red (Over.homMk x₀ hx₀ : Over.mk (spMap φ) ⟶ G) g`. Use `(red_iff_reduction U g _).2 fun e => ?_` and prove the remaining obligations. Establish `he : GlobalTheory.FormalPoint.reduction I (Over.homMk x₀ hx₀ : Over.mk (spMap φ) ⟶ G) e = y e`.

Rewrite using `[← cancel_mono (fstG I e G).left, GlobalTheory.FormalPoint.reduction_fstG]`. Conclude with `hxn e`. Rewrite using `[he]`. Conclude with `hy e`. Conclude with `⟨_, hred, fun x' hx' => red_unique hx' hred⟩`.
-/
theorem existsUnique_red [IsAdicComplete (I.map φ) S] (g : GtPt D (Over.mk (spMap φ))) :
    ∃! x : Over.mk (spMap φ) ⟶ G, U.Red x g := by
  have hy : ∀ e, ∃ y, Coords U e g (adicLevelι (I.map φ) (e + 1)) y := fun e =>
    exists_coords U e g (adicLevelι (I.map φ) (e + 1)) (GlobalTheory.FormalPoint.levelMap I φ e)
      (GlobalTheory.FormalPoint.levelMap_thick I φ e)
  choose y hy using hy
  have htf : ∀ n, thickMap R I n G ≫ (fstG I (n + 1) G).left = (fstG I n G).left := by
    intro n
    unfold thickMap fstG
    simp only [pullback.map, Category.comp_id]
    exact pullback.lift_fst _ _ _

  have hcomp : ∀ n, GlobalTheory.adicLevelMap (I.map φ) (Nat.le_succ (n + 1)) ≫ y (n + 1) = y n ≫ thickMap R I n G := by
    intro n
    refine Coords.unique ?_ (Coords.succ (hy n))
    have hk := Coords.comp (hy (n + 1)) (GlobalTheory.adicLevelMap (I.map φ) (Nat.le_succ (n + 1)))
    rwa [GlobalTheory.adicLevelMap_ι] at hk
  have hf : GlobalTheory.IsAdicFamily (I.map φ) (fun n => y n ≫ (fstG I n G).left) := by
    intro n
    show GlobalTheory.adicLevelMap (I.map φ) (Nat.le_succ (n + 1)) ≫ y (n + 1) ≫ (fstG I (n + 1) G).left =
      y n ≫ (fstG I n G).left
    rw [← Category.assoc, hcomp n, Category.assoc, htf n]
  have hs : ∀ n, (y n ≫ (fstG I n G).left) ≫ G.hom = adicLevelι (I.map φ) (n + 1) ≫ spMap φ := by
    intro n
    have ef : (fstG I n G).left ≫ G.hom = (thickObj R I n G).hom ≫ thick R I n := Over.w (fstG I n G)
    rw [Category.assoc, ef]
    exact (comp_hom_eq_of_coords (hy n)).symm

  obtain ⟨x₀, ⟨hx₀, hxn⟩, -⟩ := GlobalTheory.existsUnique_over_of_isAdicFamily (spMap φ) G.hom hf hs
  have hred : U.Red (Over.homMk x₀ hx₀ : Over.mk (spMap φ) ⟶ G) g := by
    refine (red_iff_reduction U g _).2 fun e => ?_
    have he : GlobalTheory.FormalPoint.reduction I (Over.homMk x₀ hx₀ : Over.mk (spMap φ) ⟶ G) e = y e := by
      rw [← cancel_mono (fstG I e G).left, GlobalTheory.FormalPoint.reduction_fstG]
      exact hxn e
    rw [he]
    exact hy e
  exact ⟨_, hred, fun x' hx' => red_unique hx' hred⟩

end Complete

/- English proof (translation)
Introduce `V _ _ _ _ D A G _ _ U W _ _ _ hW g`. Take `⟨-, -, -, -, hc⟩` from `hW`. Conclude with `existsUnique_red (φ := algebraMap V W) U g`.
-/
theorem main : (AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ g : GtPt D (TA V W), ∃! x : TA V W ⟶ G, U.Red x g) := by
  intro V _ _ _ _ D A G _ _ U W _ _ _ hW g
  obtain ⟨-, -, -, -, hc⟩ := hW
  exact existsUnique_red (φ := algebraMap V W) U g

end GlobalTheory.UU.RedOnto

end
