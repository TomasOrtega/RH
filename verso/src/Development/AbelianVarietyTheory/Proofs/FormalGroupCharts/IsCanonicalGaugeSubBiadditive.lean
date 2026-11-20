import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp.Regauge
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

/- English proof (translation)
The claim follows from `MvPowerSeries.ext fun e => h e.degree e le_rfl`.
-/
theorem eq_of_forall_jeq {R σ : Type} [CommRing R] {f g : MvPowerSeries σ R} (h : ∀ m, JEq m f g) : f = g :=
  MvPowerSeries.ext fun e => h e.degree e le_rfl

/- English proof (translation)
Introduce `R _ d O _ _ B k _ _ _ h g hc hg`. Establish `hF : ∀ i, MvPowerSeries.constantCoeff (B.FK k i) = 0` using `fun i => by`. Simplify using `[FB.FK, FGLaw.mapF, B.G.const]`. Establish `hA : ∀ a, GP (B.actK k a)` using `fun a i => by simp [FB.actK, B.A.const]`. Establish `gA : ∀ {n : ℕ} (i j : Fin n), GP (addOf (B.FK k) (pt k d i) (pt k d j))` using `fun i j => gp_addOf _ hF _ _ (gp_pt i) (gp_pt j)`.

Establish `gC : ∀ {n : ℕ} (a : O) (i : Fin n), GP (comp1 (B.actK k a) (pt k d i))` using `fun a i => gp_comp1 _ _ (hA a) (gp_pt i)`. Establish `a0` using `eq_of_forall_jeq fun m => (hg m).ax0`. Establish `a1` using `eq_of_forall_jeq fun m => (hg m).ax1`. Establish `d1` using `eq_of_forall_jeq fun m => (hg m).add1`. Establish `d2` using `eq_of_forall_jeq fun m => (hg m).add2`.

Establish `sy` using `eq_of_forall_jeq fun m => (hg m).sym`. Establish `bal` using `fun a => eq_of_forall_jeq fun m => (hg m).bal a`. Use `⟨?_, ?_, ?_, ?_, ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[gt_ev_sub _ (pair_points_zero_constant gp_zero₂ (gp_pt _)), hc.ax0, a0, sub_zero]`. Rewrite using `[gt_ev_sub _ (pair_points_zero_constant (gp_pt _) gp_zero₂), hc.ax1, a1, sub_zero]`.

Rewrite using `[hc.ph1, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gA _ _) (gp_pt _)), d1]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc.ph2, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gA _ _)), d2]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc.sy, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), sy]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc.ad a, gt_ev_sub _ (pair_points_zero_constant (gC _ _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gC _ _)), bal a]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isCanonGauge_sub : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h g : PS k 2 d), B.IsCanonGauge k h → (∀ m, Biadd m B k g) → B.IsCanonGauge k (h - g) := by
  intro R _ d O _ _ B k _ _ _ h g hc hg
  have hF : ∀ i, MvPowerSeries.constantCoeff (B.FK k i) = 0 := fun i => by
    simp [FB.FK, FGLaw.mapF, B.G.const]
  have hA : ∀ a, GP (B.actK k a) := fun a i => by simp [FB.actK, B.A.const]
  have gA : ∀ {n : ℕ} (i j : Fin n), GP (addOf (B.FK k) (pt k d i) (pt k d j)) :=
    fun i j => gp_addOf _ hF _ _ (gp_pt i) (gp_pt j)
  have gC : ∀ {n : ℕ} (a : O) (i : Fin n), GP (comp1 (B.actK k a) (pt k d i)) :=
    fun a i => gp_comp1 _ _ (hA a) (gp_pt i)
  have a0 := eq_of_forall_jeq fun m => (hg m).ax0
  have a1 := eq_of_forall_jeq fun m => (hg m).ax1
  have d1 := eq_of_forall_jeq fun m => (hg m).add1
  have d2 := eq_of_forall_jeq fun m => (hg m).add2
  have sy := eq_of_forall_jeq fun m => (hg m).sym
  have bal := fun a => eq_of_forall_jeq fun m => (hg m).bal a
  refine ⟨?_, ?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [gt_ev_sub _ (pair_points_zero_constant gp_zero₂ (gp_pt _)), hc.ax0, a0, sub_zero]
  · rw [gt_ev_sub _ (pair_points_zero_constant (gp_pt _) gp_zero₂), hc.ax1, a1, sub_zero]
  · rw [hc.ph1, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)),
      gt_ev_sub _ (pair_points_zero_constant (gA _ _) (gp_pt _)), d1]
    congr 1; ring
  · rw [hc.ph2, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)),
      gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gA _ _)), d2]
    congr 1; ring
  · rw [hc.sy, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), sy]
    congr 1; ring
  · rw [hc.ad a, gt_ev_sub _ (pair_points_zero_constant (gC _ _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gC _ _)), bal a]
    congr 1; ring

end GlobalTheory.ChartCmp.Regauge
