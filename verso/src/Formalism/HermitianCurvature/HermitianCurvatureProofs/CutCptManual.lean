import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCptDefs

namespace Formalism.FourierDecayAlt.P.TBBx5

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal ComplexOrder

noncomputable section

open Classical

def FormNonnegCpt {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) : Prop :=
  ∀ (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w →
    ∀ (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)), PBL.CV (p.T.bs j) x → 0 ≤ p.form j hj w x x

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Introduce `j hj w hw x hx` and use `hFP hA Wp Wq P p j hj w hw x hx`.
-/
theorem formNonneg_ofCpt (hA : P5.ThmPActualCpt) (hFP : PBL.FormPosCpt) (p : KB.Pl P Wp Wq) : FormNonnegCpt p :=
  fun j hj w hw x hx => hFP hA Wp Wq P p j hj w hw x hx

/- English proof (translation)
Establish `hpq : ∀ t : ℂ, 0 ≤ p.form j hj w x x + conj t * p.form j hj w x y + t * p.form j hj w y x + t * conj t * p.form j hj w y y`. Introduce `t`. Establish `hv : PBL.CV (p.T.bs j) (x + t • y)` using `PBL.cv_add hx (PBL.cv_smul t hy)`. Establish `h` using `hpos j hj w hw (x + t • y) hv`. Rewrite `h` using `[PBL.form_slC (p := p) (j := j) (hj := hj) (w := w) (x₁ := x) (x₂ := y) (y := x + t • y) (c := t) (h₁ := hx) (h₂ := hy) (hy := hv), PBL.form_srC (p := p) (j := j) (hj := hj) (w := w) (x := x) (y₁ := x) (y₂ := y) (c := t) (hx := hx) (h₁ := hx) (h₂ := hy), PBL.form_srC (p := p) (j …`.

Use `h using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `set A := p.form j hj w x x with hAdef`. Use `set B := p.form j hj w y y with hBdef`. Use `set a := p.form j hj w x y with hadef`.

Use `set b := p.form j hj w y x with hbdef`. Establish `key : ∀ t : ℂ, 0 ≤ (A + conj t * a + t * b + t * conj t * B).re ∧ (A + conj t * a + t * b + t * conj t * B).im = 0` using `fun t => by`. Establish `h` using `Complex.le_def.mp (hpq t)`. Conclude with `⟨by simpa using h.1, by simpa using h.2.symm⟩`. Establish `hA` using `Complex.le_def.mp (hpos j hj w hw x hx)`.

Establish `hB` using `Complex.le_def.mp (hpos j hj w hw y hy)`. Establish `hAre : 0 ≤ A.re` using `by simpa using hA.1`. Establish `hBre : 0 ≤ B.re` using `by simpa using hB.1`. Establish `hAim : A.im = 0` using `by simpa using hA.2.symm`. Establish `hBim : B.im = 0` using `by simpa using hB.2.symm`.

Establish `h1` using `(key 1).2`. Establish `h2` using `(key Complex.I).2`. Simplify using `[Complex.conj_re, Complex.conj_im, hAim, hBim] at h1 h2`. Establish `hbim : b.im = -a.im` using `by linarith`. Establish `hbre : b.re = a.re` using `by linarith`.

Establish `hs : ∀ s : ℝ, 0 ≤ (‖a‖ ^ 2 * B.re) * (s * s) + (-2 * ‖a‖ ^ 2) * s + A.re`. Introduce `s`. Establish `h` using `(key (-(s : ℂ) * a)).1`. Simplify using `[Complex.conj_re, Complex.conj_im, hAim, hBim] at h`. Rewrite `h` using `[hbre, hbim]`.

Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Use polynomial arithmetic with `[h]`. Establish `hd` using `discrim_le_zero hs`. Unfold `discrim at hd`. Establish `hc0 : 0 ≤ ‖a‖ ^ 2` using `sq_nonneg _`.

Break down `hc0.lt_or_eq with hc | hc` into its components or cases. Establish `h3 : ‖a‖ ^ 2 * ‖a‖ ^ 2 ≤ ‖a‖ ^ 2 * (A.re * B.re)` using `by nlinarith`. Conclude with `le_of_mul_le_mul_left h3 hc`. Rewrite using `[← hc]`. Conclude with `mul_nonneg hAre hBre`.
-/
theorem form_csCpt (p : KB.Pl P Wp Wq) (hpos : FormNonnegCpt p) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)
    (hw : KB.CutWord P p.l0 w) (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : PBL.CV (p.T.bs j) x) (hy : PBL.CV (p.T.bs j) y) :
    ‖p.form j hj w x y‖ ^ 2 ≤ (p.form j hj w x x).re * (p.form j hj w y y).re := by

  have hpq : ∀ t : ℂ, 0 ≤ p.form j hj w x x + conj t * p.form j hj w x y + t * p.form j hj w y x +
      t * conj t * p.form j hj w y y := by
    intro t
    have hv : PBL.CV (p.T.bs j) (x + t • y) := PBL.cv_add hx (PBL.cv_smul t hy)
    have h := hpos j hj w hw (x + t • y) hv
    rw [PBL.form_slC (p := p) (j := j) (hj := hj) (w := w) (x₁ := x) (x₂ := y) (y := x + t • y) (c := t)
        (h₁ := hx) (h₂ := hy) (hy := hv),
      PBL.form_srC (p := p) (j := j) (hj := hj) (w := w) (x := x) (y₁ := x) (y₂ := y) (c := t)
        (hx := hx) (h₁ := hx) (h₂ := hy),
      PBL.form_srC (p := p) (j := j) (hj := hj) (w := w) (x := y) (y₁ := x) (y₂ := y) (c := t)
        (hx := hy) (h₁ := hx) (h₂ := hy)] at h
    convert h using 1
    ring
  set A := p.form j hj w x x with hAdef
  set B := p.form j hj w y y with hBdef
  set a := p.form j hj w x y with hadef
  set b := p.form j hj w y x with hbdef
  have key : ∀ t : ℂ, 0 ≤ (A + conj t * a + t * b + t * conj t * B).re ∧
      (A + conj t * a + t * b + t * conj t * B).im = 0 := fun t => by
    have h := Complex.le_def.mp (hpq t)
    exact ⟨by simpa using h.1, by simpa using h.2.symm⟩
  have hA := Complex.le_def.mp (hpos j hj w hw x hx)
  have hB := Complex.le_def.mp (hpos j hj w hw y hy)
  have hAre : 0 ≤ A.re := by simpa using hA.1
  have hBre : 0 ≤ B.re := by simpa using hB.1
  have hAim : A.im = 0 := by simpa using hA.2.symm
  have hBim : B.im = 0 := by simpa using hB.2.symm

  have h1 := (key 1).2
  have h2 := (key Complex.I).2
  simp [Complex.conj_re, Complex.conj_im, hAim, hBim] at h1 h2
  have hbim : b.im = -a.im := by linarith
  have hbre : b.re = a.re := by linarith

  have hs : ∀ s : ℝ, 0 ≤ (‖a‖ ^ 2 * B.re) * (s * s) + (-2 * ‖a‖ ^ 2) * s + A.re := by
    intro s
    have h := (key (-(s : ℂ) * a)).1
    simp [Complex.conj_re, Complex.conj_im, hAim, hBim] at h
    rw [hbre, hbim] at h
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [h]
  have hd := discrim_le_zero hs
  unfold discrim at hd
  have hc0 : 0 ≤ ‖a‖ ^ 2 := sq_nonneg _
  rcases hc0.lt_or_eq with hc | hc
  · have h3 : ‖a‖ ^ 2 * ‖a‖ ^ 2 ≤ ‖a‖ ^ 2 * (A.re * B.re) := by nlinarith
    exact le_of_mul_le_mul_left h3 hc
  · rw [← hc]
    exact mul_nonneg hAre hBre

/- English proof (translation)
Establish `h` using `hpos j hj w hw x hx`. Conclude with `(Complex.le_def.mp h).1`.
-/
theorem form_re_nonnegCpt (p : KB.Pl P Wp Wq) (hpos : FormNonnegCpt p) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)
    (hw : KB.CutWord P p.l0 w) (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : PBL.CV (p.T.bs j) x) : 0 ≤ (p.form j hj w x x).re := by
  have h := hpos j hj w hw x hx
  exact (Complex.le_def.mp h).1

end place

section lift

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Introduce `b s hb hs hbs h hh w hw hlen t t' ht ht'`. Establish `ha0 : D.IsLocPt (h ++ [(s, t)]) (b + s - 1)` using `li_locPt h b s t hb hs hh ht`. Establish `ha0' : D.IsLocPt (h ++ [(s, t')]) (b + s - 1)` using `li_locPt h b s t' hb hs hh ht'`. Take `⟨grid, hgr⟩` from `hgrid b s hb hs hbs w hw hlen`. Generalize the expression as in `hJ : b + s - 1 = j at hbs ha0 ha0' grid hgr ⊢`.

Establish `hcv : ∀ (w' : List C.Letter) (a0 : C.LPt) (h0 : D.IsLocPt a0 j), PBL.CV (p.T.bs j) (KB.slv p.T F j hbs w' a0 h0.2)` using `fun w' a0 h0 e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ P p F j hbs w' a0 h0 hF e`. Establish `hf0 : ∀ (w' : List C.Letter) (a0 : C.LPt) (h0 : D.IsLocPt a0 j), KB.CutWord P p.l0 w' → 0 ≤ (p.form j hbs w' (KB.slv p.T F j hbs w' a0 h0.2) (KB.slv p.T F j hbs w' a0 h0.2)).re` using `fun w' a0 h0 hw' => form_re_nonnegCpt p hpos j hbs w' hw' _ (hcv w' a0 h0)`. Establish `hEw0 : ∀ (w' : List C.Letter) (a0 : C.LPt) (h0 : D.IsLocPt a0 j), KB.CutWord P p.l0 w' → 0 ≤ TBB.Ew p nn F j w' a0`. Introduce `w' a0 h0 hw'`. Rewrite using `[li_ew p nn F j hbs w' a0 h0]`.

Conclude with `mul_nonneg (div_nonneg (mul_self_nonneg _) (normC_pos nn hnn w').le) (hf0 w' a0 h0 hw')`. Establish `hc : 0 < TBB.normC nn w` using `normC_pos nn hnn w`. Establish `key1 : ∀ (sA sA' c R fa fb : ℝ), 0 ≤ sA → 0 ≤ sA' → 0 < c → 0 ≤ fa → 0 ≤ fb → R ^ 2 ≤ fa * fb → sA * sA' / c * R ≤ (sA * sA / c * fa + sA' * sA' / c * fb) / 2`. Introduce `sA sA' c R fa fb h1 h2 h3 h4 h5 h6`. Establish `hR : R ≤ Real.sqrt fa * Real.sqrt fb`.

Rewrite using `[← Real.sqrt_mul h4]`. Conclude with `(le_abs_self R).trans (Real.abs_le_sqrt h6)`. Establish `e1` using `Real.sq_sqrt h4`. Establish `e2` using `Real.sq_sqrt h5`. Establish `h7 : sA * sA' * R ≤ (sA * sA * fa + sA' * sA' * fb) / 2`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hR (mul_nonneg h1 h2), sq_nonneg (sA * Real.sqrt fa - sA' * Real.sqrt fb)]`. Establish `e3 : sA * sA' / c * R = (sA * sA' * R) / c` using `by ring`. Establish `e4 : (sA * sA / c * fa + sA' * sA' / c * fb) / 2 = ((sA * sA * fa + sA' * sA' * fb) / 2) / c`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3, e4]`.

Conclude with `div_le_div_of_nonneg_right h7 h3.le`. Establish `hcs` using `form_csCpt p hpos j hbs w hw.1 _ _ (hcv w _ ha0) (hcv w _ ha0')`. Establish `b1 : ‖TBB.NP p nn F j w (h ++ [(s, t)]) (h ++ [(s, t')])‖ ≤ (TBB.Ew p nn F j w (h ++ [(s, t)]) + TBB.Ew p nn F j w (h ++ [(s, t')])) / 2`. Rewrite using `[li_np p nn F j hbs w _ _ ha0 ha0', li_ew p nn F j hbs w _ ha0, li_ew p nn F j hbs w _ ha0', norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hc.le)]`. Conclude with `key1 _ _ _ _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hc (hf0 w _ ha0 hw.1) (hf0 w _ ha0' hw.1) hcs`.

Establish `hnode : ∀ n : Fin K → Fin (2 * (j - s) + s + 1), Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w * ‖KB.pairJ (p.form j hbs w) (ysOf grid n) (KB.slv p.T F j hbs (KB.plusW (ysOf grid n) w) _ ha0.2) …`. Introduce `n`. Take `⟨hcp, hcm, hpw⟩` from `hgr.2.2.1 n`. Take `⟨hq, hSS2⟩` from `hSS hA _ _ P p j hbs w (ysOf grid n) hcp hcm hpw`. Establish `hq0 : 0 < ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod`.

Apply `List.prod_pos` to reduce the goal to its premises. Introduce `z hz`. Take `⟨y, hy, rfl⟩` from `List.mem_map.mp hz`. Conclude with `hq y hy`. Establish `hP1` using `prod_map_pos nn hnn (ysOf grid n)`.

Establish `hP2` using `prod_map_pos (fun y => nn (y + 1)) (fun y => hnn _) (ysOf grid n)`. Establish `hcs2` using `hSS2 _ _ (hcv _ _ ha0) (hcv _ _ ha0')`. Rewrite using `[li_ew p nn F j hbs _ _ ha0, li_ew p nn F j hbs _ _ ha0', normC_plusW, normC_minusW]`. Establish `hsc` using `scal_cs (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w) (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) / TBB.normC nn w) (Real …`. Use `hsc using 3` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `all_goals field_simp`. Take `⟨n₀, hn₀⟩` from `sum_le_max (fun n : Fin K → Fin (2 * (j - s) + s + 1) => |∏ a, F7.lagCo (grid a) (n a)| * Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod / ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod)) (fun n => Real.s …`. Take `⟨hcp₀, hcm₀, -⟩` from `hgr.2.2.1 n₀`. Establish `b2 : ‖t⁻¹ - t'⁻¹‖ ^ K * ‖TBB.NP p nn F j w (h ++ [(s, t)]) (h ++ [(s, t')])‖ ≤ Λ ^ K * ((TBB.Ew p nn F j (KB.plusW (ysOf grid n₀) w) (h ++ [(s, t)]) + TBB.Ew p nn F j (KB.minusW (ysOf grid n₀) w) (h ++ [(s, t')])) / 2)`. Establish `hDL'` using `hDL _ _ P p F j s hbs w h h t t' ha0 ha0' K grid hF hgr.1`.

Rewrite `hDL'` using `[PBL.rr_eq_form p F j hbs w _ _ ha0 ha0']`. Establish `hnorm : ‖t⁻¹ - t'⁻¹‖ ^ K * ‖p.form j hbs w (KB.slv p.T F j hbs w _ ha0.2) (KB.slv p.T F j hbs w _ ha0'.2)‖ ≤ ∑ n : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (n a)| * ‖KB.pairJ (p.form j hbs w) (ysOf grid n) (KB.slv p.T F j hbs (KB.plusW (ysOf grid n) w) _ ha0.2) …`. Establish `e : ‖t⁻¹ - t'⁻¹‖ ^ K * ‖p.form j hbs w (KB.slv p.T F j hbs w _ ha0.2) (KB.slv p.T F j hbs w _ ha0'.2)‖ = ‖((-1 : ℂ) ^ (s - 1) * (t⁻¹ - t'⁻¹)) ^ K * p.form j hbs w (KB.slv p.T F j hbs w _ ha0.2) (KB.slv p.T F j hbs w _ ha0'.2)‖`. Rewrite using `[norm_mul, norm_pow, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]`. Rewrite using `[e, hDL']`.

Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Both sides reduce to the same expression. Rewrite using `[li_np p nn F j hbs w _ _ ha0 ha0', norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hc.le)]`.

Establish `hα0 : 0 ≤ Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w` using `div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hc.le`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ ∑ n : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (n a)| * Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod / ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) * Real.sqrt (TBB.Ew p nn F j …`. Use `Finset.sum_le_sum fun n _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (hnode n) (abs_nonneg _)`. Use `_ ≤ Λ ^ K * Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n₀) w) (h ++ [(s, t)]) * TBB.Ew p nn F j (KB.minusW (ysOf grid n₀) w) (h ++ [(s, t')])) := hn₀`.

Use `_ ≤ _ := by`. Establish `hl : 0 ≤ Λ ^ K`. Establish `hsum0` using `hgr.2.2.2`. Conclude with `le_trans (Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hsum0`. Conclude with `mul_le_mul_of_nonneg_left (sqrt_mul_le_avg _ _ (hEw0 _ _ ha0 hcp₀) (hEw0 _ _ ha0' hcm₀)) hl`.

Break down `mn_pick Λ ‖t⁻¹ - t'⁻¹‖ _ _ _ K (norm_nonneg _) b1 (fun _ => b2) with h1 | h2` into its components or cases. Conclude with `⟨w, w, isExt_self P p.l0 Y N K w hw (by omega), isExt_self P p.l0 Y N K w hw (by omega), h1⟩`. Establish `hlenK : (ysOf grid n₀).length = K` using `by simp [ysOf]`. Conclude with `⟨KB.plusW (ysOf grid n₀) w, KB.minusW (ysOf grid n₀) w, isExt_plusW P p.l0 Y N K w (ysOf grid n₀) hlen hlenK (ysOf_mem grid hgr.2.1 n₀) hcp₀, isExt_minusW P p.l0 Y N K w (ysOf grid n₀) hlen hlenK (ysOf_mem grid hgr.2.1 n₀) hcm₀, h2⟩`.
-/
theorem integral_four_at_place_of_partsCpt (hA : P5.ThmPActualCpt) (hSS : KB.SizeStdCpt) (hDL : KB.DegLift) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) (hpos : FormNonnegCpt p)
    (hF : KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y) (hgrid : LiftGrid p nn Y Λ K N) :
    TBB.KernelArgumentHypothesisScalar p nn F Y Λ K N := by
  intro b s hb hs hbs h hh w hw hlen t t' ht ht'
  have ha0 : D.IsLocPt (h ++ [(s, t)]) (b + s - 1) := li_locPt h b s t hb hs hh ht
  have ha0' : D.IsLocPt (h ++ [(s, t')]) (b + s - 1) := li_locPt h b s t' hb hs hh ht'
  obtain ⟨grid, hgr⟩ := hgrid b s hb hs hbs w hw hlen
  generalize hJ : b + s - 1 = j at hbs ha0 ha0' grid hgr ⊢

  have hcv : ∀ (w' : List C.Letter) (a0 : C.LPt) (h0 : D.IsLocPt a0 j),
      PBL.CV (p.T.bs j) (KB.slv p.T F j hbs w' a0 h0.2) :=
    fun w' a0 h0 e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ P p F j hbs w' a0 h0 hF e
  have hf0 : ∀ (w' : List C.Letter) (a0 : C.LPt) (h0 : D.IsLocPt a0 j), KB.CutWord P p.l0 w' →
      0 ≤ (p.form j hbs w' (KB.slv p.T F j hbs w' a0 h0.2) (KB.slv p.T F j hbs w' a0 h0.2)).re :=
    fun w' a0 h0 hw' => form_re_nonnegCpt p hpos j hbs w' hw' _ (hcv w' a0 h0)
  have hEw0 : ∀ (w' : List C.Letter) (a0 : C.LPt) (h0 : D.IsLocPt a0 j), KB.CutWord P p.l0 w' →
      0 ≤ TBB.Ew p nn F j w' a0 := by
    intro w' a0 h0 hw'
    rw [li_ew p nn F j hbs w' a0 h0]
    exact mul_nonneg (div_nonneg (mul_self_nonneg _) (normC_pos nn hnn w').le) (hf0 w' a0 h0 hw')
  have hc : 0 < TBB.normC nn w := normC_pos nn hnn w

  have key1 : ∀ (sA sA' c R fa fb : ℝ), 0 ≤ sA → 0 ≤ sA' → 0 < c → 0 ≤ fa → 0 ≤ fb → R ^ 2 ≤ fa * fb →
      sA * sA' / c * R ≤ (sA * sA / c * fa + sA' * sA' / c * fb) / 2 := by
    intro sA sA' c R fa fb h1 h2 h3 h4 h5 h6
    have hR : R ≤ Real.sqrt fa * Real.sqrt fb := by
      rw [← Real.sqrt_mul h4]
      exact (le_abs_self R).trans (Real.abs_le_sqrt h6)
    have e1 := Real.sq_sqrt h4
    have e2 := Real.sq_sqrt h5
    have h7 : sA * sA' * R ≤ (sA * sA * fa + sA' * sA' * fb) / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hR (mul_nonneg h1 h2),
        sq_nonneg (sA * Real.sqrt fa - sA' * Real.sqrt fb)]
    have e3 : sA * sA' / c * R = (sA * sA' * R) / c := by ring
    have e4 : (sA * sA / c * fa + sA' * sA' / c * fb) / 2 = ((sA * sA * fa + sA' * sA' * fb) / 2) / c := by
      ring
    rw [e3, e4]
    exact div_le_div_of_nonneg_right h7 h3.le
  have hcs := form_csCpt p hpos j hbs w hw.1 _ _ (hcv w _ ha0) (hcv w _ ha0')
  have b1 : ‖TBB.NP p nn F j w (h ++ [(s, t)]) (h ++ [(s, t')])‖ ≤
      (TBB.Ew p nn F j w (h ++ [(s, t)]) + TBB.Ew p nn F j w (h ++ [(s, t')])) / 2 := by
    rw [li_np p nn F j hbs w _ _ ha0 ha0', li_ew p nn F j hbs w _ ha0, li_ew p nn F j hbs w _ ha0',
      norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hc.le)]
    exact key1 _ _ _ _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hc (hf0 w _ ha0 hw.1)
      (hf0 w _ ha0' hw.1) hcs

  have hnode : ∀ n : Fin K → Fin (2 * (j - s) + s + 1),
      Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) *
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w *
        ‖KB.pairJ (p.form j hbs w) (ysOf grid n)
          (KB.slv p.T F j hbs (KB.plusW (ysOf grid n) w) _ ha0.2)
          (KB.slv p.T F j hbs (KB.minusW (ysOf grid n) w) _ ha0'.2)‖ ≤
      Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod /
        ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
      Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n) w) (h ++ [(s, t)]) *
        TBB.Ew p nn F j (KB.minusW (ysOf grid n) w) (h ++ [(s, t')])) := by
    intro n
    obtain ⟨hcp, hcm, hpw⟩ := hgr.2.2.1 n
    obtain ⟨hq, hSS2⟩ := hSS hA _ _ P p j hbs w (ysOf grid n) hcp hcm hpw
    have hq0 : 0 < ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod := by
      apply List.prod_pos
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact hq y hy
    have hP1 := prod_map_pos nn hnn (ysOf grid n)
    have hP2 := prod_map_pos (fun y => nn (y + 1)) (fun y => hnn _) (ysOf grid n)
    have hcs2 := hSS2 _ _ (hcv _ _ ha0) (hcv _ _ ha0')
    rw [li_ew p nn F j hbs _ _ ha0, li_ew p nn F j hbs _ _ ha0', normC_plusW, normC_minusW]
    have hsc := scal_cs
      (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) *
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w)
      (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) *
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) / TBB.normC nn w)
      (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) *
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w)
      _ _ _ _ _ _
      (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hc.le)
      (by ring)
      (div_nonneg (mul_self_nonneg _) hc.le) (div_nonneg (mul_self_nonneg _) hc.le)
      hq0 hP1 hP2 (norm_nonneg _) (hf0 _ _ ha0 hcp) (hf0 _ _ ha0' hcm) hcs2
    convert hsc using 3
    all_goals field_simp

  obtain ⟨n₀, hn₀⟩ := sum_le_max
    (fun n : Fin K → Fin (2 * (j - s) + s + 1) => |∏ a, F7.lagCo (grid a) (n a)| *
      Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod /
        ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod))
    (fun n => Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n) w) (h ++ [(s, t)]) *
        TBB.Ew p nn F j (KB.minusW (ysOf grid n) w) (h ++ [(s, t')])))
    (Λ ^ K) (fun n => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (fun n => Real.sqrt_nonneg _)
    hgr.2.2.2
  obtain ⟨hcp₀, hcm₀, -⟩ := hgr.2.2.1 n₀
  have b2 : ‖t⁻¹ - t'⁻¹‖ ^ K * ‖TBB.NP p nn F j w (h ++ [(s, t)]) (h ++ [(s, t')])‖ ≤
      Λ ^ K * ((TBB.Ew p nn F j (KB.plusW (ysOf grid n₀) w) (h ++ [(s, t)]) +
        TBB.Ew p nn F j (KB.minusW (ysOf grid n₀) w) (h ++ [(s, t')])) / 2) := by
    have hDL' := hDL _ _ P p F j s hbs w h h t t' ha0 ha0' K grid hF hgr.1
    rw [PBL.rr_eq_form p F j hbs w _ _ ha0 ha0'] at hDL'
    have hnorm : ‖t⁻¹ - t'⁻¹‖ ^ K *
        ‖p.form j hbs w (KB.slv p.T F j hbs w _ ha0.2) (KB.slv p.T F j hbs w _ ha0'.2)‖ ≤
        ∑ n : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (n a)| *
          ‖KB.pairJ (p.form j hbs w) (ysOf grid n)
            (KB.slv p.T F j hbs (KB.plusW (ysOf grid n) w) _ ha0.2)
            (KB.slv p.T F j hbs (KB.minusW (ysOf grid n) w) _ ha0'.2)‖ := by
      have e : ‖t⁻¹ - t'⁻¹‖ ^ K *
          ‖p.form j hbs w (KB.slv p.T F j hbs w _ ha0.2) (KB.slv p.T F j hbs w _ ha0'.2)‖ =
          ‖((-1 : ℂ) ^ (s - 1) * (t⁻¹ - t'⁻¹)) ^ K *
            p.form j hbs w (KB.slv p.T F j hbs w _ ha0.2) (KB.slv p.T F j hbs w _ ha0'.2)‖ := by
        rw [norm_mul, norm_pow, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      rw [e, hDL']
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rfl
    rw [li_np p nn F j hbs w _ _ ha0 ha0', norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hc.le)]
    have hα0 : 0 ≤ Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) *
        Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w :=
      div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hc.le
    calc ‖t⁻¹ - t'⁻¹‖ ^ K * (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) *
          Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w *
          ‖p.form j hbs w (KB.slv p.T F j hbs w _ ha0.2) (KB.slv p.T F j hbs w _ ha0'.2)‖)
        = Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) *
          Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w *
          (‖t⁻¹ - t'⁻¹‖ ^ K *
            ‖p.form j hbs w (KB.slv p.T F j hbs w _ ha0.2) (KB.slv p.T F j hbs w _ ha0'.2)‖) := by ring
      _ ≤ Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) *
          Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w *
          ∑ n : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (n a)| *
            ‖KB.pairJ (p.form j hbs w) (ysOf grid n)
              (KB.slv p.T F j hbs (KB.plusW (ysOf grid n) w) _ ha0.2)
              (KB.slv p.T F j hbs (KB.minusW (ysOf grid n) w) _ ha0'.2)‖ :=
          mul_le_mul_of_nonneg_left hnorm hα0
      _ = ∑ n : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (n a)| *
            (Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t)])) *
              Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(s, t')])) / TBB.normC nn w *
            ‖KB.pairJ (p.form j hbs w) (ysOf grid n)
              (KB.slv p.T F j hbs (KB.plusW (ysOf grid n) w) _ ha0.2)
              (KB.slv p.T F j hbs (KB.minusW (ysOf grid n) w) _ ha0'.2)‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
      _ ≤ ∑ n : Fin K → Fin (2 * (j - s) + s + 1), |∏ a, F7.lagCo (grid a) (n a)| *
            Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod /
              ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
            Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n) w) (h ++ [(s, t)]) *
              TBB.Ew p nn F j (KB.minusW (ysOf grid n) w) (h ++ [(s, t')])) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hnode n) (abs_nonneg _)
      _ ≤ Λ ^ K * Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n₀) w) (h ++ [(s, t)]) *
              TBB.Ew p nn F j (KB.minusW (ysOf grid n₀) w) (h ++ [(s, t')])) := hn₀
      _ ≤ _ := by
          have hl : 0 ≤ Λ ^ K := by
            have hsum0 := hgr.2.2.2
            exact le_trans (Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hsum0
          exact mul_le_mul_of_nonneg_left (sqrt_mul_le_avg _ _ (hEw0 _ _ ha0 hcp₀) (hEw0 _ _ ha0' hcm₀)) hl
  rcases mn_pick Λ ‖t⁻¹ - t'⁻¹‖ _ _ _ K (norm_nonneg _) b1 (fun _ => b2) with h1 | h2
  · exact ⟨w, w, isExt_self P p.l0 Y N K w hw (by omega), isExt_self P p.l0 Y N K w hw (by omega), h1⟩
  · have hlenK : (ysOf grid n₀).length = K := by simp [ysOf]
    exact ⟨KB.plusW (ysOf grid n₀) w, KB.minusW (ysOf grid n₀) w,
      isExt_plusW P p.l0 Y N K w (ysOf grid n₀) hlen hlenK (ysOf_mem grid hgr.2.1 n₀) hcp₀,
      isExt_minusW P p.l0 Y N K w (ysOf grid n₀) hlen hlenK (ysOf_mem grid hgr.2.1 n₀) hcm₀, h2⟩

end lift

section wave

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Introduce `j hj h hh w hw hlen s`. Take `⟨grid, hgr⟩` from `hgrid j hj w hw hlen`. Establish `hcv : ∀ (w' : List C.Letter), PBL.CV (p.T.bs j) (KB.slv p.T F j hj w' h hh.2)` using `fun w' e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ P p F j hj w' h hh hF e`. Establish `hf0 : ∀ (w' : List C.Letter), KB.CutWord P p.l0 w' → 0 ≤ (p.form j hj w' (KB.slv p.T F j hj w' h hh.2) (KB.slv p.T F j hj w' h hh.2)).re` using `fun w' hw' => form_re_nonnegCpt p hpos j hj w' hw' _ (hcv w')`. Establish `hn0` using `weighted_auxiliary_norm_nonneg P j hj h hh`.

Establish `hEw0 : ∀ (w' : List C.Letter), KB.CutWord P p.l0 w' → 0 ≤ TBB.Ew p nn F j w' h`. Introduce `w' hw'`. Rewrite using `[wv_ew p nn F j hj w' h hh]`. Conclude with `mul_nonneg (div_nonneg hn0 (normC_pos nn hnn w').le) (hf0 w' hw')`. Establish `hc : 0 < TBB.normC nn w` using `normC_pos nn hnn w`.

Establish `hVw : ∀ (w' : List C.Letter), KB.CutWord P p.l0 w' → PBL.CV (p.T.bs j) (KB.waveG (p.T.bs j) s w' (KB.slv p.T F j hj w' h hh.2)) ∧ p.form j hj w' (KB.waveG (p.T.bs j) s w' (KB.slv p.T F j hj w' h hh.2)) (KB.waveG (p.T.bs j) s w' (KB.slv p.T F j hj w' h hh.2)) = p.form j hj w' (KB. …`. Introduce `w' hw'`. Take `⟨h1, h2⟩` from `hVI hA _ _ P p j hj w' hw' s _ _ (hcv w') (hcv w')`. Conclude with `⟨h1, h2⟩`. Take `⟨φ, -, -, hφ, hint⟩` from `hPS hA _ _ P p F j hj w h h hh hh Cb hCb hF hw.1`.

Establish `hI : ∫ c, P5.fsv s c * TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) = ((C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w : ℝ) : ℂ) * p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h hh.2)`. Rewrite using `[← hint s, ← integral_const_mul]`. Use `integral_congr_ae (PBL.ae_ne_zero_complex.mono fun c hc0 => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← wv_np p nn F j hj h hh w c, hφ c hc0]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hα0 : 0 ≤ C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w` using `div_nonneg hn0 hc.le`. Establish `b1 : ‖∫ c, P5.fsv s c * TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ ≤ TBB.Ew p nn F j w h`. Rewrite using `[hI, norm_mul, Complex.norm_real, Real.norm_of_nonneg hα0, wv_ew p nn F j hj w h hh]`. Use `mul_le_mul_of_nonneg_left ?_ hα0` and prove the remaining obligations.

Establish `hcs` using `form_csCpt p hpos j hj w hw.1 _ _ (hVw w hw.1).1 (hcv w)`. Rewrite `hcs` using `[(hVw w hw.1).2]`. Establish `hf` using `hf0 w hw.1`. Use polynomial arithmetic with `[norm_nonneg (p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h hh.2))]`. Establish `hnode : ∀ n : Fin K → Fin (2 * j + 1), C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w * ‖KB.pairJ (p.form j hj w) (ysOf grid n) (KB.waveG (p.T.bs j) s (KB.plusW (ysOf grid n) w) (KB.slv p.T F j hj (KB.plusW (ysOf grid n) w) h hh.2)) (KB.slv p.T F j hj (KB.minusW (ysOf grid …`.

Introduce `n`. Take `⟨hcp, hcm, hpw⟩` from `hgr.2.2.1 n`. Take `⟨hq, hSS2⟩` from `hSS hA _ _ P p j hj w (ysOf grid n) hcp hcm hpw`. Establish `hq0 : 0 < ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod`. Apply `List.prod_pos` to reduce the goal to its premises.

Introduce `z hz`. Take `⟨y, hy, rfl⟩` from `List.mem_map.mp hz`. Conclude with `hq y hy`. Establish `hP1` using `prod_map_pos nn hnn (ysOf grid n)`. Establish `hP2` using `prod_map_pos (fun y => nn (y + 1)) (fun y => hnn _) (ysOf grid n)`.

Establish `hcs2` using `hSS2 _ _ (hVw _ hcp).1 (hcv _)`. Rewrite `hcs2` using `[(hVw _ hcp).2]`. Rewrite using `[wv_ew p nn F j hj _ h hh, wv_ew p nn F j hj _ h hh, normC_plusW, normC_minusW]`. Establish `hsc` using `scal_cs (C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w) (C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w) (C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w) _ _ _ _ _ _ hα0 (by ring) hα0 hα0 hq0 hP1 hP2 (norm_nonneg _) (hf0 _ hcp) (hf0 _ hcm) hcs2`. Use `hsc using 3` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `all_goals field_simp`. Take `⟨n₀, hn₀⟩` from `sum_le_max (fun n : Fin K → Fin (2 * j + 1) => |∏ a, F7.lagCo (grid a) (n a)| * Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod / ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod)) (fun n => Real.sqrt (TBB.E …`. Take `⟨hcp₀, hcm₀, -⟩` from `hgr.2.2.1 n₀`. Establish `b2 : ‖s‖ ^ K * ‖∫ c, P5.fsv s c * TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ ≤ Λ ^ K * max (TBB.Ew p nn F j (KB.plusW (ysOf grid n₀) w) h) (TBB.Ew p nn F j (KB.minusW (ysOf grid n₀) w) h)`. Establish `hD` using `hDW _ _ P p F j hj w h h hh hh K grid s LinearMap.id (fun ε x hx e => hx e) hF hgr.1`.

Rewrite `hD` using `[PBL.onOld_id]`. Simplify using `only [LinearMap.id_apply] at hD`. Establish `hnorm : ‖s‖ ^ K * ‖p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h hh.2)‖ ≤ ∑ n : Fin K → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| * ‖KB.pairJ (p.form j hj w) (ysOf grid n) (KB.waveG (p.T.bs j) s (KB.plusW (ysOf grid n) w) (KB.sl …`. Rewrite using `[← norm_pow, ← norm_mul, hD]`. Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Both sides reduce to the same expression. Establish `hl : 0 ≤ Λ ^ K` using `le_trans (Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hgr.2.2.2`. Rewrite using `[hI, norm_mul, Complex.norm_real, Real.norm_of_nonneg hα0]`.

Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w * ∑ n : Fin K → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| * ‖KB.pairJ (p.form j hj w) (ysOf grid n) (KB.waveG (p.T.bs j) s (KB.plusW (ysOf grid n) w) (KB.slv p.T F j hj (KB.plusW (ysOf grid n) w) h hh.2)) (KB.slv p.T …`. Use `_ = ∑ n : Fin K → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| * (C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w * ‖KB.pairJ (p.form j hj w) (ysOf grid n) (KB.waveG (p.T.bs j) s (KB.plusW (ysOf grid n) w) (KB.slv p.T F j hj (KB.plusW (ysOf grid n) w) h hh.2)) (KB.slv p.T …`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ∑ n : Fin K → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| * Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod / ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) * Real.sqrt (TBB.Ew p nn F j (KB.plusW …`. Use `Finset.sum_le_sum fun n _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`.

Conclude with `mul_le_mul_of_nonneg_left (hnode n) (abs_nonneg _)`. Use `_ ≤ Λ ^ K * Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n₀) w) h * TBB.Ew p nn F j (KB.minusW (ysOf grid n₀) w) h) := hn₀`. Use `_ ≤ _ := mul_le_mul_of_nonneg_left (sqrt_mul_le_max _ _ (hEw0 _ hcp₀) (hEw0 _ hcm₀)) hl`. Establish `hlenK : (ysOf grid n₀).length = K` using `by simp [ysOf]`. Break down `mn_pick Λ ‖s‖ _ _ _ K (norm_nonneg _) b1 (fun _ => b2) with h1 | h2` into its components or cases.

Conclude with `⟨w, isExt_self P p.l0 Y N K w hw (by omega), h1⟩`. Break down `le_total (TBB.Ew p nn F j (KB.minusW (ysOf grid n₀) w) h) (TBB.Ew p nn F j (KB.plusW (ysOf grid n₀) w) h) with hle | hle` into its components or cases. Rewrite `h2` using `[max_eq_left hle]`. Conclude with `⟨KB.plusW (ysOf grid n₀) w, isExt_plusW P p.l0 Y N K w (ysOf grid n₀) hlen hlenK (ysOf_mem grid hgr.2.1 n₀) hcp₀, h2⟩`. Rewrite `h2` using `[max_eq_right hle]`.

Conclude with `⟨KB.minusW (ysOf grid n₀) w, isExt_minusW P p.l0 Y N K w (ysOf grid n₀) hlen hlenK (ysOf_mem grid hgr.2.1 n₀) hcm₀, h2⟩`.
-/
theorem integral_three_at_place_of_partsCpt (hA : P5.ThmPActualCpt) (hPS : KB.PStdCpt) (hVI : KB.VIsoCpt) (hSS : KB.SizeStdCpt) (hDW : KB.DegWave)
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ)
    (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hpos : FormNonnegCpt p) (hF : KB.CptCoef p.T.base F)
    (hnn : ∀ y, 0 < nn y) (hgrid : WaveGrid p nn Y Λ K N) : TBB.KernelFourierIntegralBound p nn F Y Λ K N := by
  intro j hj h hh w hw hlen s
  obtain ⟨grid, hgr⟩ := hgrid j hj w hw hlen
  have hcv : ∀ (w' : List C.Letter), PBL.CV (p.T.bs j) (KB.slv p.T F j hj w' h hh.2) :=
    fun w' e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ P p F j hj w' h hh hF e
  have hf0 : ∀ (w' : List C.Letter), KB.CutWord P p.l0 w' →
      0 ≤ (p.form j hj w' (KB.slv p.T F j hj w' h hh.2) (KB.slv p.T F j hj w' h hh.2)).re :=
    fun w' hw' => form_re_nonnegCpt p hpos j hj w' hw' _ (hcv w')
  have hn0 := weighted_auxiliary_norm_nonneg P j hj h hh
  have hEw0 : ∀ (w' : List C.Letter), KB.CutWord P p.l0 w' → 0 ≤ TBB.Ew p nn F j w' h := by
    intro w' hw'
    rw [wv_ew p nn F j hj w' h hh]
    exact mul_nonneg (div_nonneg hn0 (normC_pos nn hnn w').le) (hf0 w' hw')
  have hc : 0 < TBB.normC nn w := normC_pos nn hnn w

  have hVw : ∀ (w' : List C.Letter), KB.CutWord P p.l0 w' →
      PBL.CV (p.T.bs j) (KB.waveG (p.T.bs j) s w' (KB.slv p.T F j hj w' h hh.2)) ∧
      p.form j hj w' (KB.waveG (p.T.bs j) s w' (KB.slv p.T F j hj w' h hh.2))
        (KB.waveG (p.T.bs j) s w' (KB.slv p.T F j hj w' h hh.2)) =
      p.form j hj w' (KB.slv p.T F j hj w' h hh.2) (KB.slv p.T F j hj w' h hh.2) := by
    intro w' hw'
    obtain ⟨h1, h2⟩ := hVI hA _ _ P p j hj w' hw' s _ _ (hcv w') (hcv w')
    exact ⟨h1, h2⟩

  obtain ⟨φ, -, -, hφ, hint⟩ := hPS hA _ _ P p F j hj w h h hh hh Cb hCb hF hw.1
  have hI : ∫ c, P5.fsv s c * TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) =
      ((C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w : ℝ) : ℂ) *
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h hh.2) := by
    rw [← hint s, ← integral_const_mul]
    refine integral_congr_ae (PBL.ae_ne_zero_complex.mono fun c hc0 => ?_)
    dsimp only
    rw [← wv_np p nn F j hj h hh w c, hφ c hc0]
    ring
  have hα0 : 0 ≤ C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w := div_nonneg hn0 hc.le

  have b1 : ‖∫ c, P5.fsv s c * TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ ≤
      TBB.Ew p nn F j w h := by
    rw [hI, norm_mul, Complex.norm_real, Real.norm_of_nonneg hα0, wv_ew p nn F j hj w h hh]
    refine mul_le_mul_of_nonneg_left ?_ hα0
    have hcs := form_csCpt p hpos j hj w hw.1 _ _ (hVw w hw.1).1 (hcv w)
    rw [(hVw w hw.1).2] at hcs
    have hf := hf0 w hw.1
    nlinarith [norm_nonneg (p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2))
      (KB.slv p.T F j hj w h hh.2))]

  have hnode : ∀ n : Fin K → Fin (2 * j + 1),
      C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w *
        ‖KB.pairJ (p.form j hj w) (ysOf grid n)
          (KB.waveG (p.T.bs j) s (KB.plusW (ysOf grid n) w) (KB.slv p.T F j hj (KB.plusW (ysOf grid n) w) h hh.2))
          (KB.slv p.T F j hj (KB.minusW (ysOf grid n) w) h hh.2)‖ ≤
      Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod /
        ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
      Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n) w) h *
        TBB.Ew p nn F j (KB.minusW (ysOf grid n) w) h) := by
    intro n
    obtain ⟨hcp, hcm, hpw⟩ := hgr.2.2.1 n
    obtain ⟨hq, hSS2⟩ := hSS hA _ _ P p j hj w (ysOf grid n) hcp hcm hpw
    have hq0 : 0 < ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod := by
      apply List.prod_pos
      intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact hq y hy
    have hP1 := prod_map_pos nn hnn (ysOf grid n)
    have hP2 := prod_map_pos (fun y => nn (y + 1)) (fun y => hnn _) (ysOf grid n)
    have hcs2 := hSS2 _ _ (hVw _ hcp).1 (hcv _)
    rw [(hVw _ hcp).2] at hcs2
    rw [wv_ew p nn F j hj _ h hh, wv_ew p nn F j hj _ h hh, normC_plusW, normC_minusW]
    have hsc := scal_cs
      (C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w)
      (C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w)
      (C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w)
      _ _ _ _ _ _ hα0 (by ring) hα0 hα0 hq0 hP1 hP2 (norm_nonneg _) (hf0 _ hcp) (hf0 _ hcm) hcs2
    convert hsc using 3
    all_goals field_simp
  obtain ⟨n₀, hn₀⟩ := sum_le_max
    (fun n : Fin K → Fin (2 * j + 1) => |∏ a, F7.lagCo (grid a) (n a)| *
      Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod /
        ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod))
    (fun n => Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n) w) h *
        TBB.Ew p nn F j (KB.minusW (ysOf grid n) w) h))
    (Λ ^ K) (fun n => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (fun n => Real.sqrt_nonneg _)
    hgr.2.2.2
  obtain ⟨hcp₀, hcm₀, -⟩ := hgr.2.2.1 n₀
  have b2 : ‖s‖ ^ K * ‖∫ c, P5.fsv s c * TBB.NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ ≤
      Λ ^ K * max (TBB.Ew p nn F j (KB.plusW (ysOf grid n₀) w) h)
        (TBB.Ew p nn F j (KB.minusW (ysOf grid n₀) w) h) := by
    have hD := hDW _ _ P p F j hj w h h hh hh K grid s LinearMap.id (fun ε x hx e => hx e) hF hgr.1
    simp_rw [PBL.onOld_id] at hD
    simp only [LinearMap.id_apply] at hD
    have hnorm : ‖s‖ ^ K *
        ‖p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h hh.2)‖ ≤
        ∑ n : Fin K → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| *
          ‖KB.pairJ (p.form j hj w) (ysOf grid n)
            (KB.waveG (p.T.bs j) s (KB.plusW (ysOf grid n) w)
              (KB.slv p.T F j hj (KB.plusW (ysOf grid n) w) h hh.2))
            (KB.slv p.T F j hj (KB.minusW (ysOf grid n) w) h hh.2)‖ := by
      rw [← norm_pow, ← norm_mul, hD]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rfl
    have hl : 0 ≤ Λ ^ K :=
      le_trans (Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hgr.2.2.2
    rw [hI, norm_mul, Complex.norm_real, Real.norm_of_nonneg hα0]
    calc ‖s‖ ^ K * (C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w *
          ‖p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h hh.2)‖)
        = C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w * (‖s‖ ^ K *
          ‖p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h hh.2)‖) := by
          ring
      _ ≤ C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w *
          ∑ n : Fin K → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| *
            ‖KB.pairJ (p.form j hj w) (ysOf grid n)
              (KB.waveG (p.T.bs j) s (KB.plusW (ysOf grid n) w)
                (KB.slv p.T F j hj (KB.plusW (ysOf grid n) w) h hh.2))
              (KB.slv p.T F j hj (KB.minusW (ysOf grid n) w) h hh.2)‖ :=
          mul_le_mul_of_nonneg_left hnorm hα0
      _ = ∑ n : Fin K → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| *
            (C.nAux P.k P.r 0 (fun _ _ => 1) 1 h / TBB.normC nn w *
            ‖KB.pairJ (p.form j hj w) (ysOf grid n)
              (KB.waveG (p.T.bs j) s (KB.plusW (ysOf grid n) w)
                (KB.slv p.T F j hj (KB.plusW (ysOf grid n) w) h hh.2))
              (KB.slv p.T F j hj (KB.minusW (ysOf grid n) w) h hh.2)‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
      _ ≤ ∑ n : Fin K → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| *
            Real.sqrt (((ysOf grid n).map nn).prod * ((ysOf grid n).map fun y => nn (y + 1)).prod /
              ((ysOf grid n).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re).prod) *
            Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n) w) h *
              TBB.Ew p nn F j (KB.minusW (ysOf grid n) w) h) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (hnode n) (abs_nonneg _)
      _ ≤ Λ ^ K * Real.sqrt (TBB.Ew p nn F j (KB.plusW (ysOf grid n₀) w) h *
              TBB.Ew p nn F j (KB.minusW (ysOf grid n₀) w) h) := hn₀
      _ ≤ _ := mul_le_mul_of_nonneg_left (sqrt_mul_le_max _ _ (hEw0 _ hcp₀) (hEw0 _ hcm₀)) hl
  have hlenK : (ysOf grid n₀).length = K := by simp [ysOf]
  rcases mn_pick Λ ‖s‖ _ _ _ K (norm_nonneg _) b1 (fun _ => b2) with h1 | h2
  · exact ⟨w, isExt_self P p.l0 Y N K w hw (by omega), h1⟩
  · rcases le_total (TBB.Ew p nn F j (KB.minusW (ysOf grid n₀) w) h)
      (TBB.Ew p nn F j (KB.plusW (ysOf grid n₀) w) h) with hle | hle
    · rw [max_eq_left hle] at h2
      exact ⟨KB.plusW (ysOf grid n₀) w,
        isExt_plusW P p.l0 Y N K w (ysOf grid n₀) hlen hlenK (ysOf_mem grid hgr.2.1 n₀) hcp₀, h2⟩
    · rw [max_eq_right hle] at h2
      exact ⟨KB.minusW (ysOf grid n₀) w,
        isExt_minusW P p.l0 Y N K w (ysOf grid n₀) hlen hlenK (ysOf_mem grid hgr.2.1 n₀) hcm₀, h2⟩

end wave

end

end Formalism.FourierDecayAlt.P.TBBx5

/- English proof (translation)
Introduce `hRH hHT`. Use `first`. Consider the case `exact fun hP => Formalism.FourierDecayAlt.P.PBO.pStdCpt_of_heads hP hRH hHT`. Consider the case `(intro hP; exact Formalism.FourierDecayAlt.P.PBO.pStdCpt_of_heads hP hRH hHT)`. Consider the case `(unfold Formalism.FourierDecayAlt.KB.PStdCpt; exact fun hP => Formalism.FourierDecayAlt.P.PBO.pStdCpt_of_heads hP hRH hHT)`.
-/
theorem Formalism.FourierDecayAlt.P.standard_pairing_of_headsCpt : Formalism.FourierDecayAlt.KB.RadHead → Formalism.FourierDecayAlt.KB.HeadTop → Formalism.FourierDecayAlt.KB.PStdCpt := by
  intro hRH hHT
  first
    | exact fun hP => Formalism.FourierDecayAlt.P.PBO.pStdCpt_of_heads hP hRH hHT
    | (intro hP; exact Formalism.FourierDecayAlt.P.PBO.pStdCpt_of_heads hP hRH hHT)
    | (unfold Formalism.FourierDecayAlt.KB.PStdCpt; exact fun hP => Formalism.FourierDecayAlt.P.PBO.pStdCpt_of_heads hP hRH hHT)

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal ComplexOrder

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Use `Formalism.FourierDecayAlt.P.TBBx3.posAt_of_forms p nn F Y N hnn (fun j w h hj hw _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hh : D.IsLocPt h j`. Establish `hrr : p.RR F j w h h = p.form j hj w (KB.slv p.T F j hj w h hh.2) (KB.slv p.T F j hj w h hh.2)`. Unfold `KB.Pl.RR D.RRplace`. Rewrite using `[dif_pos ⟨hh, hh⟩, dif_pos hj]`.

Both sides reduce to the same expression. Rewrite using `[hrr]`. Establish `hx` using `Formalism.FourierDecayAlt.P.module_form_pos_compact_support hA _ _ P p j hj w hw.1 (KB.slv p.T F j hj w h hh.2) (fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ P p F j hj w h hh hF e)`. Conclude with `(Complex.le_def.mp hx).1`. Establish `hrr : p.RR F j w h h = 0`.

Unfold `KB.Pl.RR D.RRplace`. Rewrite using `[dif_neg (fun hc => hh hc.1)]`. Rewrite using `[hrr]`. Simplify using the standard rewrite rules.
-/
theorem posAt_of_cptCpt (hA : P5.ThmPActualCpt) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (hnn : ∀ y, 0 ≤ nn y)
    (hF : KB.CptCoef p.T.base F) : TBB.PosAt p nn F Y N := by
  refine Formalism.FourierDecayAlt.P.TBBx3.posAt_of_forms p nn F Y N hnn (fun j w h hj hw _ => ?_)
  by_cases hh : D.IsLocPt h j
  · have hrr : p.RR F j w h h =
        p.form j hj w (KB.slv p.T F j hj w h hh.2) (KB.slv p.T F j hj w h hh.2) := by
      unfold KB.Pl.RR D.RRplace
      rw [dif_pos ⟨hh, hh⟩, dif_pos hj]
      rfl
    rw [hrr]
    have hx := Formalism.FourierDecayAlt.P.module_form_pos_compact_support hA _ _ P p j hj w hw.1 (KB.slv p.T F j hj w h hh.2)
      (fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ P p F j hj w h hh hF e)
    exact (Complex.le_def.mp hx).1
  · have hrr : p.RR F j w h h = 0 := by
      unfold KB.Pl.RR D.RRplace
      rw [dif_neg (fun hc => hh hc.1)]
    rw [hrr]
    simp

/- English proof (translation)
Introduce `w hw _`. Distinguish the cases in `hh : D.IsLocPt ([] : C.LPt) 0`. Establish `hrr : p.RR F 0 w [] [] = p.form 0 (Nat.zero_le _) w (KB.slv p.T F 0 (Nat.zero_le _) w [] hh.2) (KB.slv p.T F 0 (Nat.zero_le _) w [] hh.2)`. Unfold `KB.Pl.RR D.RRplace`. Rewrite using `[dif_pos ⟨hh, hh⟩, dif_pos (Nat.zero_le _)]`.

Both sides reduce to the same expression. Rewrite using `[hrr]`. Establish `hx` using `Formalism.FourierDecayAlt.P.module_form_pos_compact_support hA _ _ P p 0 (Nat.zero_le _) w hw.1 (KB.slv p.T F 0 (Nat.zero_le _) w [] hh.2) (fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ P p F 0 (Nat.zero_le _) w [] hh hF e)`. Conclude with `(Complex.le_def.mp hx).1`. Establish `hrr : p.RR F 0 w [] [] = 0`.

Unfold `KB.Pl.RR D.RRplace`. Rewrite using `[dif_neg (fun hc => hh hc.1)]`. Rewrite using `[hrr]`. Simplify using the standard rewrite rules.
-/
theorem truncated_limit_positivity_holdsCpt (hA : P5.ThmPActualCpt) (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) (Y : Finset ℝ) (N : ℕ) : LimPos p F Y N := by
  intro w hw _
  by_cases hh : D.IsLocPt ([] : C.LPt) 0
  · have hrr : p.RR F 0 w [] [] =
        p.form 0 (Nat.zero_le _) w (KB.slv p.T F 0 (Nat.zero_le _) w [] hh.2)
          (KB.slv p.T F 0 (Nat.zero_le _) w [] hh.2) := by
      unfold KB.Pl.RR D.RRplace
      rw [dif_pos ⟨hh, hh⟩, dif_pos (Nat.zero_le _)]
      rfl
    rw [hrr]
    have hx := Formalism.FourierDecayAlt.P.module_form_pos_compact_support hA _ _ P p 0 (Nat.zero_le _) w hw.1
      (KB.slv p.T F 0 (Nat.zero_le _) w [] hh.2)
      (fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ P p F 0 (Nat.zero_le _) w [] hh hF e)
    exact (Complex.le_def.mp hx).1
  · have hrr : p.RR F 0 w [] [] = 0 := by
      unfold KB.Pl.RR D.RRplace
      rw [dif_neg (fun hc => hh hc.1)]
    rw [hrr]
    simp

end place

/- English proof (translation)
Introduce `hA Wp Wq _ _ _ _ _ _ P p nn F Y N Cb hCb hF hnn i hi w hw hN`. Establish `hpos : TBBx5.FormNonnegCpt p` using `TBBx5.formNonneg_ofCpt hA (Formalism.FourierDecayAlt.P.module_form_pos_compact_support : PBL.FormPosCpt) p`. Establish `hnC : 0 < TBB.normC nn w`. Unfold `TBB.normC`. Use `List.prod_pos fun x hx => ?_` and prove the remaining obligations.

Take `⟨l, _, rfl⟩` from `List.mem_map.1 hx`. Conclude with `hnn _`. Use `set c0 : ℝ := 1 / TBB.normC nn w with hc0`. Establish `hc0n : 0 ≤ c0` using `by positivity`. Set `sq : C.LPt → ℝ` to `fun a => Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a)`.

Set `u : C.LPt → (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - i) → (Wq →L[ℂ] Wp))` to `fun a => if ha : D.IsLocPt a i then ((sq a : ℝ) : ℂ) • KB.slv p.T F i hi w a ha.2 else 0`. Establish `hslv : ∀ a (ha : D.IsLocPt a i), PBL.CV (p.T.bs i) (KB.slv p.T F i hi w a ha.2)` using `fun a ha e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F i hi w a ha hF e`. Establish `hu : ∀ a, PBL.CV (p.T.bs i) (u a)`. Introduce `a`. Distinguish the cases in `ha : D.IsLocPt a i`.

Simplify using `only [u, dif_pos ha]`. Conclude with `PBL.cv_smul _ (hslv a ha)`. Simplify using `only [u, dif_neg ha]`. Conclude with `PBL.cv_zero`. Set `β : (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - i) → (Wq →L[ℂ] Wp)) → (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - i) → (Wq →L[ℂ] Wp)) → ℂ` to `fun x y => (c0 : ℂ) * p.form i hi w x y`.

Establish `hpsd : ∀ Y' : Finset C.LPt, TB.PSDOn Y' (fun a b => β (u a) (u b))`. Introduce `Y'`. Use `PBL.gram_psd (PBL.CV (S := Fin w.length) (p.T.bs i)) β PBL.cv_zero (fun x y hx hy => PBL.cv_add hx hy) (fun c x hx => PBL.cv_smul c hx) ?_ ?_ ?_ Y' u hu` and prove the remaining obligations. Introduce `x₁ x₂ y c h₁ h₂ hy`. Simplify using `only [β, PBL.form_slC p i hi w x₁ x₂ y c h₁ h₂ hy]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `x y₁ y₂ c hx h₁ h₂`. Simplify using `only [β, PBL.form_srC p i hi w x y₁ y₂ c hx h₁ h₂]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x hx`.

Conclude with `mul_nonneg (by exact_mod_cast hc0n) (hpos i hi w hw.1 x hx)`. Take `⟨H, i1, i2, i3, V, hV⟩` from `Formalism.FourierDecayAlt.P.GermFibreKernels.kolmogorov _ hpsd`. Use `⟨H, i1, i2, i3, V, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[← hV]`. Simplify using `only [β]`.

Distinguish the cases in `ha : D.IsLocPt a i`. Distinguish the cases in `hb : D.IsLocPt b i`. Simplify using `only [u, dif_pos ha, dif_pos hb]`. Rewrite using `[formC_smul_l p i hi w _ _ _ (hslv a ha) (PBL.cv_smul _ (hslv b hb)), formC_smul_r p i hi w _ _ _ (hslv a ha) (hslv b hb), Complex.conj_ofReal]`. Establish `hrr : p.RR F i w a b = p.form i hi w (KB.slv p.T F i hi w a ha.2) (KB.slv p.T F i hi w b hb.2)`.

Unfold `KB.Pl.RR D.RRplace`. Rewrite using `[dif_pos ⟨ha, hb⟩, dif_pos hi]`. Both sides reduce to the same expression. Unfold `TBB.NP`. Rewrite using `[hrr, hc0]`.

Simplify using `only [sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [u, dif_neg hb]`. Rewrite using `[formC_zero_r p i hi w _ (hu a)]`.

Unfold `TBB.NP KB.Pl.RR D.RRplace`. Rewrite using `[dif_neg (fun h => hb h.2)]`. Simplify using the standard rewrite rules. Simplify using `only [u, dif_neg ha]`. Rewrite using `[formC_zero_l p i hi w _ (hu b)]`.

Unfold `TBB.NP KB.Pl.RR D.RRplace`. Rewrite using `[dif_neg (fun h => ha h.1)]`. Simplify using the standard rewrite rules.
-/
theorem glGramCpt : GLGramCpt := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y N Cb hCb hF hnn i hi w hw hN
  have hpos : TBBx5.FormNonnegCpt p :=
    TBBx5.formNonneg_ofCpt hA (Formalism.FourierDecayAlt.P.module_form_pos_compact_support : PBL.FormPosCpt) p
  have hnC : 0 < TBB.normC nn w := by
    unfold TBB.normC
    refine List.prod_pos fun x hx => ?_
    obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
    exact hnn _
  set c0 : ℝ := 1 / TBB.normC nn w with hc0
  have hc0n : 0 ≤ c0 := by positivity
  let sq : C.LPt → ℝ := fun a => Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a)
  let u : C.LPt → (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - i) → (Wq →L[ℂ] Wp)) := fun a =>
    if ha : D.IsLocPt a i then ((sq a : ℝ) : ℂ) • KB.slv p.T F i hi w a ha.2 else 0
  have hslv : ∀ a (ha : D.IsLocPt a i), PBL.CV (p.T.bs i) (KB.slv p.T F i hi w a ha.2) :=
    fun a ha e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F i hi w a ha hF e
  have hu : ∀ a, PBL.CV (p.T.bs i) (u a) := by
    intro a
    by_cases ha : D.IsLocPt a i
    · simp only [u, dif_pos ha]; exact PBL.cv_smul _ (hslv a ha)
    · simp only [u, dif_neg ha]; exact PBL.cv_zero
  let β : (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - i) → (Wq →L[ℂ] Wp)) →
      (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - i) → (Wq →L[ℂ] Wp)) → ℂ :=
    fun x y => (c0 : ℂ) * p.form i hi w x y
  have hpsd : ∀ Y' : Finset C.LPt, TB.PSDOn Y' (fun a b => β (u a) (u b)) := by
    intro Y'
    refine PBL.gram_psd (PBL.CV (S := Fin w.length) (p.T.bs i)) β PBL.cv_zero (fun x y hx hy => PBL.cv_add hx hy)
      (fun c x hx => PBL.cv_smul c hx) ?_ ?_ ?_ Y' u hu
    · intro x₁ x₂ y c h₁ h₂ hy
      simp only [β, PBL.form_slC p i hi w x₁ x₂ y c h₁ h₂ hy]; ring
    · intro x y₁ y₂ c hx h₁ h₂
      simp only [β, PBL.form_srC p i hi w x y₁ y₂ c hx h₁ h₂]; ring
    · intro x hx
      exact mul_nonneg (by exact_mod_cast hc0n) (hpos i hi w hw.1 x hx)
  obtain ⟨H, i1, i2, i3, V, hV⟩ := Formalism.FourierDecayAlt.P.GermFibreKernels.kolmogorov _ hpsd
  refine ⟨H, i1, i2, i3, V, fun a b => ?_⟩
  rw [← hV]
  simp only [β]
  by_cases ha : D.IsLocPt a i
  · by_cases hb : D.IsLocPt b i
    · simp only [u, dif_pos ha, dif_pos hb]
      rw [formC_smul_l p i hi w _ _ _ (hslv a ha) (PBL.cv_smul _ (hslv b hb)),
        formC_smul_r p i hi w _ _ _ (hslv a ha) (hslv b hb), Complex.conj_ofReal]
      have hrr : p.RR F i w a b = p.form i hi w (KB.slv p.T F i hi w a ha.2) (KB.slv p.T F i hi w b hb.2) := by
        unfold KB.Pl.RR D.RRplace
        rw [dif_pos ⟨ha, hb⟩, dif_pos hi]
        rfl
      unfold TBB.NP
      rw [hrr, hc0]
      simp only [sq]
      push_cast
      ring
    · simp only [u, dif_neg hb]
      rw [formC_zero_r p i hi w _ (hu a)]
      unfold TBB.NP KB.Pl.RR D.RRplace
      rw [dif_neg (fun h => hb h.2)]
      simp
  · simp only [u, dif_neg ha]
    rw [formC_zero_l p i hi w _ (hu b)]
    unfold TBB.NP KB.Pl.RR D.RRplace
    rw [dif_neg (fun h => ha h.1)]
    simp

end

end Formalism.FourierDecayAlt.P.CutBP
