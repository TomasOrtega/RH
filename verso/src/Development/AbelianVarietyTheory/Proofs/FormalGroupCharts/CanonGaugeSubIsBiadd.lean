import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ d O _ _ k _ _ _ B h h' hh hh'`. Establish `hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n` using `n) d j) := fun j => gp_pt j`. Establish `hz : ∀ {n : ℕ}, GP (0 : Pt k n d)` using `gp_zero₂`. Establish `hF : ∀ i, constantCoeff (B.FK k i) = 0` using `fun i => by`. Simplify using `only [FB.FK, FGLaw.mapF, MvPowerSeries.constantCoeff_map, B.G.const i, map_zero]`.

Establish `hA : ∀ a, GP (B.actK k a)` using `fun a i => by`. Simplify using `only [FB.actK, MvPowerSeries.constantCoeff_map, B.A.const a i, map_zero]`. Establish `h0 : constantCoeff h = 0`. Use `congrArg constantCoeff hh.ax0` as an intermediate fact. Rewrite `this` using `[gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_zero]`. Then use the resulting hypothesis.

Establish `h0' : constantCoeff h' = 0`. Use `congrArg constantCoeff hh'.ax0` as an intermediate fact. Rewrite `this` using `[gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_zero]`. Then use the resulting hypothesis. Establish `inj : ∀ {n : ℕ} {a b : PS k n d}, constantCoeff a = 0 → constantCoeff b = 0 → FB.expS k a = FB.expS k b → a = b` using `fun ha hb e => exp_inj ha hb e`. Use `⟨?_, ?_, ?_, ?_, fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[gt_ev_sub _ (pair_points_zero_constant hz (hp 0)), hh.ax0, hh'.ax0, sub_zero]`. Rewrite using `[gt_ev_sub _ (pair_points_zero_constant (hp 0) hz), hh.ax1, hh'.ax1, sub_zero]`. Establish `a1` using `pair_points_zero_constant (hp (n := 3) 0) (hp 2)`. Establish `a2` using `pair_points_zero_constant (hp (n := 3) 1) (hp 2)`. Establish `a3` using `pair_points_zero_constant (gp_addOf _ hF _ _ (hp (n := 3) 0) (hp 1)) (hp 2)`.

Establish `e` using `inj (by rw [map_sub, map_add, gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, gt_const_ev _ a3 _ h0]; simp) (by rw [map_sub, map_add, gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', gt_const_ev _ a3 _ h0']; simp) (hh.ph1.symm.trans hh'.ph1)`. Rewrite using `[gt_ev_sub _ a1, gt_ev_sub _ a2, gt_ev_sub _ a3]`. Take the linear combination `-e`. Establish `a1` using `pair_points_zero_constant (hp (n := 3) 0) (hp 1)`. Establish `a2` using `pair_points_zero_constant (hp (n := 3) 0) (hp 2)`.

Establish `a3` using `pair_points_zero_constant (hp (n := 3) 0) (gp_addOf _ hF _ _ (hp (n := 3) 1) (hp 2))`. Establish `e` using `inj (by rw [map_sub, map_add, gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, gt_const_ev _ a3 _ h0]; simp) (by rw [map_sub, map_add, gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', gt_const_ev _ a3 _ h0']; simp) (hh.ph2.symm.trans hh'.ph2)`. Rewrite using `[gt_ev_sub _ a1, gt_ev_sub _ a2, gt_ev_sub _ a3]`. Take the linear combination `-e`. Establish `a1` using `pair_points_zero_constant (gp_comp1 _ _ (hA a) (hp (n := 2) 0)) (hp 1)`.

Establish `a2` using `pair_points_zero_constant (hp (n := 2) 0) (gp_comp1 _ _ (hA (star a)) (hp (n := 2) 1))`. Establish `e` using `inj (by rw [map_sub, gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, sub_zero]) (by rw [map_sub, gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', sub_zero]) ((hh.ad a).symm.trans (hh'.ad a))`. Rewrite using `[gt_ev_sub _ a1, gt_ev_sub _ a2]`. Take the linear combination `-e`.
-/
theorem canonGauge_sub_isBiadd : G2.CanonicalGaugeDiffBiadditive := by
  intro R _ d O _ _ k _ _ _ B h h' hh hh'
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hF : ∀ i, constantCoeff (B.FK k i) = 0 := fun i => by
    simp only [FB.FK, FGLaw.mapF, MvPowerSeries.constantCoeff_map, B.G.const i, map_zero]
  have hA : ∀ a, GP (B.actK k a) := fun a i => by
    simp only [FB.actK, MvPowerSeries.constantCoeff_map, B.A.const a i, map_zero]
  have h0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_zero] at this
  have h0' : constantCoeff h' = 0 := by
    have := congrArg constantCoeff hh'.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_zero] at this
  have inj : ∀ {n : ℕ} {a b : PS k n d}, constantCoeff a = 0 → constantCoeff b = 0 →
      FB.expS k a = FB.expS k b → a = b := fun ha hb e => exp_inj ha hb e
  refine ⟨?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [gt_ev_sub _ (pair_points_zero_constant hz (hp 0)), hh.ax0, hh'.ax0, sub_zero]
  · rw [gt_ev_sub _ (pair_points_zero_constant (hp 0) hz), hh.ax1, hh'.ax1, sub_zero]
  · have a1 := pair_points_zero_constant (hp (n := 3) 0) (hp 2)
    have a2 := pair_points_zero_constant (hp (n := 3) 1) (hp 2)
    have a3 := pair_points_zero_constant (gp_addOf _ hF _ _ (hp (n := 3) 0) (hp 1)) (hp 2)
    have e := inj
      (by rw [map_sub, map_add, gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, gt_const_ev _ a3 _ h0]; simp)
      (by rw [map_sub, map_add, gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', gt_const_ev _ a3 _ h0']; simp)
      (hh.ph1.symm.trans hh'.ph1)
    rw [gt_ev_sub _ a1, gt_ev_sub _ a2, gt_ev_sub _ a3]
    linear_combination -e
  · have a1 := pair_points_zero_constant (hp (n := 3) 0) (hp 1)
    have a2 := pair_points_zero_constant (hp (n := 3) 0) (hp 2)
    have a3 := pair_points_zero_constant (hp (n := 3) 0) (gp_addOf _ hF _ _ (hp (n := 3) 1) (hp 2))
    have e := inj
      (by rw [map_sub, map_add, gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, gt_const_ev _ a3 _ h0]; simp)
      (by rw [map_sub, map_add, gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', gt_const_ev _ a3 _ h0']; simp)
      (hh.ph2.symm.trans hh'.ph2)
    rw [gt_ev_sub _ a1, gt_ev_sub _ a2, gt_ev_sub _ a3]
    linear_combination -e
  · have a1 := pair_points_zero_constant (gp_comp1 _ _ (hA a) (hp (n := 2) 0)) (hp 1)
    have a2 := pair_points_zero_constant (hp (n := 2) 0) (gp_comp1 _ _ (hA (star a)) (hp (n := 2) 1))
    have e := inj
      (by rw [map_sub, gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, sub_zero])
      (by rw [map_sub, gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', sub_zero])
      ((hh.ad a).symm.trans (hh'.ad a))
    rw [gt_ev_sub _ a1, gt_ev_sub _ a2]
    linear_combination -e

end GlobalTheory
