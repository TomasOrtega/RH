import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.SymGauge

variable {k : Type} [CommRing k] {d : ℕ}

/- English proof (translation)
Rewrite using `[gt_ev_mul V hV]`. Use `congr 1`. Unfold `ev`. Rewrite using `[MvPowerSeries.subst_C]`.
-/
theorem ev_C_mul {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (c : k) (f : PS k m d) :
    ev V (C c * f) = C c * ev V f := by
  rw [gt_ev_mul V hV]
  congr 1
  unfold ev
  rw [MvPowerSeries.subst_C]

/- English proof (translation)
The claim follows from `exp_inj hf hg h`.
-/
theorem expS_inj [Algebra ℚ k] {n : ℕ} {f g : PS k n d} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) (h : FB.expS k f = FB.expS k g) : f = g := exp_inj hf hg h

/- English proof (translation)
The claim follows from `exp_zero`.
-/
theorem expS_zero [Algebra ℚ k] {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := exp_zero

/- English proof (translation)
Introduce `k _ _ d O _ _ B h1 h2 had`. Establish `hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n` using `n) d j) := fun j => gp_pt j`. Establish `hz : ∀ {n : ℕ}, GP (0 : Pt k n d)` using `gp_zero₂`. Establish `hF : ∀ i, constantCoeff (B.G.F i) = 0` using `B.G.const`. Establish `hsy1 : constantCoeff B.sy = 1`.

Use `congrArg constantCoeff B.symmetry_zero_fst` as an intermediate fact. Rewrite `this` using `[gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_one]`. Then use the resulting hypothesis. Take `⟨s, hs0, hs⟩ : ∃ s : PS k 2 d, constantCoeff s = 0 ∧ FB.expS k s = B.sy` from `⟨_, constantCoeff_logS hsy1, exp_log hsy1⟩`. Establish `E : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → ev ![a, b] B.sy = FB.expS k (ev ![a, b] s)`. Introduce `n a b ha hb`.

Rewrite using `[← hs, gt_ev_expS _ (pair_points_zero_constant ha hb) _ hs0]`. Establish `c0 : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → constantCoeff (ev ![a, b] s) = 0` using `fun a b ha hb => gt_const_ev _ (pair_points_zero_constant ha hb) _ hs0`. Establish `anti0 : s + ev (n` using `2) ![pt k d 1, pt k d 0] s = 0 := by`. Establish `e` using `B.sy_inv`. Rewrite `e` using `[E _ _ (hp 1) (hp 0)]`.

Use `expS_inj (by rw [map_add, hs0, c0 _ _ (hp 1) (hp 0), add_zero]) (map_zero _) ?_` and prove the remaining obligations. Rewrite using `[gt_expS_add _ _ hs0 (c0 _ _ (hp 1) (hp 0)), hs, e, expS_zero]`. Establish `anti : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → ev ![b, a] s = - ev ![a, b] s`. Introduce `n a b ha hb`. Establish `hV` using `pair_points_zero_constant ha hb`.

Establish `e` using `congrArg (ev ![a, b]) anti0`. Rewrite `e` using `[gt_ev_add _ hV, gt_ev_zero _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 1) (hp 0)), eval_pair_points, evP_pt _ hV, evP_pt _ hV]`. Conclude with `eq_neg_of_add_eq_zero_right e`. Establish `add0 : ev (n` using `3) ![pt k d 0, pt k d 1] s + ev (n := 3) ![pt k d 0, pt k d 2] s = ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] s := by`. Establish `hA` using `gp_addOf _ hF _ _ (hp (n := 3) 1) (hp (n := 3) 2)`.

Establish `e` using `B.sy_law`. Rewrite `e` using `[h1, h2, ev_one, one_mul, mul_one, E _ _ (hp 0) (hp 1), E _ _ (hp 0) (hp 2), E _ _ (hp 0) hA]`. Use `expS_inj (by rw [map_add, c0 _ _ (hp 0) (hp 1), c0 _ _ (hp 0) (hp 2), add_zero]) (c0 _ _ (hp 0) hA) ?_` and prove the remaining obligations. Rewrite using `[gt_expS_add _ _ (c0 _ _ (hp 0) (hp 1)) (c0 _ _ (hp 0) (hp 2)), e]`. Establish `add2 : ∀ {n : ℕ} (x y z : Pt k n d), GP x → GP y → GP z → ev ![x, y] s + ev ![x, z] s = ev ![x, addOf B.G.F y z] s`.

Introduce `n x y z hx hy hz'`. Establish `hA` using `gp_addOf _ hF _ _ (hp (n := 3) 1) (hp (n := 3) 2)`. Establish `hV` using `triple_points_zero_constant hx hy hz'`. Establish `e` using `congrArg (ev ![x, y, z]) add0`. Rewrite `e` using `[gt_ev_add _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 1)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 2)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) hA), eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hV _ _ _ (hp 1) (hp 2 …`.

Conclude with `e`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : k, (C c : PS k 2 d) * 2 = -1 := by`. Use `⟨algebraMap ℚ k (-1 / 2), ?_⟩` and prove the remaining obligations. Establish `e : algebraMap ℚ k (-1 / 2) * 2 = -1`. Rewrite using `[← map_ofNat (algebraMap ℚ k) 2, ← map_mul]`.

Evaluate the numerical expressions. Use `congrArg (C (σ := Fin 2 × Fin d) (R := k)) e` as an intermediate fact. Rewrite `this` using `[map_mul, map_neg, map_one, map_ofNat]`. Then use the resulting hypothesis. Use `⟨C c * s, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e` using `B.symmetry_zero_fst`.

Rewrite `e` using `[E _ _ hz (hp 0), ← expS_zero]`. Rewrite using `[ev_C_mul _ (pair_points_zero_constant hz (hp 0)), expS_inj (c0 _ _ hz (hp 0)) (map_zero _) e, mul_zero]`. Establish `e` using `B.symmetry_zero_snd`. Rewrite `e` using `[E _ _ (hp 0) hz, ← expS_zero]`. Rewrite using `[ev_C_mul _ (pair_points_zero_constant (hp 0) hz), expS_inj (c0 _ _ (hp 0) hz) (map_zero _) e, mul_zero]`.

Establish `hA` using `gp_addOf _ hF _ _ (hp (n := 3) 0) (hp (n := 3) 1)`. Rewrite using `[ev_C_mul _ (pair_points_zero_constant (hp 0) (hp 2)), ev_C_mul _ (pair_points_zero_constant (hp 1) (hp 2)), ev_C_mul _ (pair_points_zero_constant hA (hp 2)), anti _ _ (hp 2) (hp 0), anti _ _ (hp 2) (hp 1), anti _ _ (hp 2) hA, ← add2 _ _ _ (hp 2) (hp 0) (hp 1)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hA` using `gp_addOf _ hF _ _ (hp (n := 3) 1) (hp (n := 3) 2)`. Rewrite using `[ev_C_mul _ (pair_points_zero_constant (hp 0) (hp 1)), ev_C_mul _ (pair_points_zero_constant (hp 0) (hp 2)), ev_C_mul _ (pair_points_zero_constant (hp 0) hA), ← add0]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `a`. Establish `hx` using `gp_comp1 _ _ (B.A.const a) (hp (n := 2) 0)`. Establish `hy` using `gp_comp1 _ _ (B.A.const (star a)) (hp (n := 2) 1)`. Establish `e` using `B.ad_sy a`.

Rewrite `e` using `[had, had, ev_one, one_mul, one_mul, E _ _ hx (hp 1), E _ _ (hp 0) hy]`. Rewrite using `[ev_C_mul _ (pair_points_zero_constant hx (hp 1)), ev_C_mul _ (pair_points_zero_constant (hp 0) hy), expS_inj (c0 _ _ hx (hp 1)) (c0 _ _ (hp 0) hy) e, sub_self]`. Rewrite using `[ev_C_mul _ (pair_points_zero_constant (hp 1) (hp 0)), ← hs]`. Use `congr 1`. Take the linear combination `(-C c) * anti0 + s * hc`.
-/
theorem exists_gauge_of_symmetry :
    ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → (∀ a, B.ad a = 1) → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ (∀ a : O, (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h) = 0) ∧ B.sy = FB.expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h) := by
  intro k _ _ d O _ _ B h1 h2 had
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hF : ∀ i, constantCoeff (B.G.F i) = 0 := B.G.const
  have hsy1 : constantCoeff B.sy = 1 := by
    have := congrArg constantCoeff B.symmetry_zero_fst
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_one] at this
  obtain ⟨s, hs0, hs⟩ : ∃ s : PS k 2 d, constantCoeff s = 0 ∧ FB.expS k s = B.sy :=
    ⟨_, constantCoeff_logS hsy1, exp_log hsy1⟩
  have E : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → ev ![a, b] B.sy = FB.expS k (ev ![a, b] s) := by
    intro n a b ha hb
    rw [← hs, gt_ev_expS _ (pair_points_zero_constant ha hb) _ hs0]
  have c0 : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → constantCoeff (ev ![a, b] s) = 0 :=
    fun a b ha hb => gt_const_ev _ (pair_points_zero_constant ha hb) _ hs0

  have anti0 : s + ev (n := 2) ![pt k d 1, pt k d 0] s = 0 := by
    have e := B.sy_inv
    rw [E _ _ (hp 1) (hp 0)] at e
    refine expS_inj (by rw [map_add, hs0, c0 _ _ (hp 1) (hp 0), add_zero]) (map_zero _) ?_
    rw [gt_expS_add _ _ hs0 (c0 _ _ (hp 1) (hp 0)), hs, e, expS_zero]
  have anti : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → ev ![b, a] s = - ev ![a, b] s := by
    intro n a b ha hb
    have hV := pair_points_zero_constant ha hb
    have e := congrArg (ev ![a, b]) anti0
    rw [gt_ev_add _ hV, gt_ev_zero _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 1) (hp 0)), eval_pair_points,
      evP_pt _ hV, evP_pt _ hV] at e
    exact eq_neg_of_add_eq_zero_right e

  have add0 : ev (n := 3) ![pt k d 0, pt k d 1] s + ev (n := 3) ![pt k d 0, pt k d 2] s =
      ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] s := by
    have hA := gp_addOf _ hF _ _ (hp (n := 3) 1) (hp (n := 3) 2)
    have e := B.sy_law
    rw [h1, h2, ev_one, one_mul, mul_one, E _ _ (hp 0) (hp 1), E _ _ (hp 0) (hp 2), E _ _ (hp 0) hA] at e
    refine expS_inj (by rw [map_add, c0 _ _ (hp 0) (hp 1), c0 _ _ (hp 0) (hp 2), add_zero])
      (c0 _ _ (hp 0) hA) ?_
    rw [gt_expS_add _ _ (c0 _ _ (hp 0) (hp 1)) (c0 _ _ (hp 0) (hp 2)), e]
  have add2 : ∀ {n : ℕ} (x y z : Pt k n d), GP x → GP y → GP z →
      ev ![x, y] s + ev ![x, z] s = ev ![x, addOf B.G.F y z] s := by
    intro n x y z hx hy hz'
    have hA := gp_addOf _ hF _ _ (hp (n := 3) 1) (hp (n := 3) 2)
    have hV := triple_points_zero_constant hx hy hz'
    have e := congrArg (ev ![x, y, z]) add0
    rw [gt_ev_add _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 1)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 2)),
      gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) hA), eval_pair_points, eval_pair_points, eval_pair_points,
      evP_addOf _ hV _ _ _ (hp 1) (hp 2), evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at e
    exact e
  obtain ⟨c, hc⟩ : ∃ c : k, (C c : PS k 2 d) * 2 = -1 := by
    refine ⟨algebraMap ℚ k (-1 / 2), ?_⟩
    have e : algebraMap ℚ k (-1 / 2) * 2 = -1 := by
      rw [← map_ofNat (algebraMap ℚ k) 2, ← map_mul]
      norm_num
    have := congrArg (C (σ := Fin 2 × Fin d) (R := k)) e
    rwa [map_mul, map_neg, map_one, map_ofNat] at this
  refine ⟨C c * s, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have e := B.symmetry_zero_fst
    rw [E _ _ hz (hp 0), ← expS_zero] at e
    rw [ev_C_mul _ (pair_points_zero_constant hz (hp 0)), expS_inj (c0 _ _ hz (hp 0)) (map_zero _) e, mul_zero]
  · have e := B.symmetry_zero_snd
    rw [E _ _ (hp 0) hz, ← expS_zero] at e
    rw [ev_C_mul _ (pair_points_zero_constant (hp 0) hz), expS_inj (c0 _ _ (hp 0) hz) (map_zero _) e, mul_zero]
  · have hA := gp_addOf _ hF _ _ (hp (n := 3) 0) (hp (n := 3) 1)
    rw [ev_C_mul _ (pair_points_zero_constant (hp 0) (hp 2)), ev_C_mul _ (pair_points_zero_constant (hp 1) (hp 2)), ev_C_mul _ (pair_points_zero_constant hA (hp 2)),
      anti _ _ (hp 2) (hp 0), anti _ _ (hp 2) (hp 1), anti _ _ (hp 2) hA,
      ← add2 _ _ _ (hp 2) (hp 0) (hp 1)]
    ring
  · have hA := gp_addOf _ hF _ _ (hp (n := 3) 1) (hp (n := 3) 2)
    rw [ev_C_mul _ (pair_points_zero_constant (hp 0) (hp 1)), ev_C_mul _ (pair_points_zero_constant (hp 0) (hp 2)), ev_C_mul _ (pair_points_zero_constant (hp 0) hA),
      ← add0]
    ring
  · intro a
    have hx := gp_comp1 _ _ (B.A.const a) (hp (n := 2) 0)
    have hy := gp_comp1 _ _ (B.A.const (star a)) (hp (n := 2) 1)
    have e := B.ad_sy a
    rw [had, had, ev_one, one_mul, one_mul, E _ _ hx (hp 1), E _ _ (hp 0) hy] at e
    rw [ev_C_mul _ (pair_points_zero_constant hx (hp 1)), ev_C_mul _ (pair_points_zero_constant (hp 0) hy),
      expS_inj (c0 _ _ hx (hp 1)) (c0 _ _ (hp 0) hy) e, sub_self]
  · rw [ev_C_mul _ (pair_points_zero_constant (hp 1) (hp 0)), ← hs]
    congr 1
    linear_combination (-C c) * anti0 + s * hc

end GlobalTheory.SymGauge
