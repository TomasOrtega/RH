import Formalism.LFunctionBounds.ExpSumLowerBound

open Complex

noncomputable section

namespace Formalism.FX

/- English proof (translation)
Establish `hc : Continuous γ` using `continuous_iff_continuousAt.2 fun t => (hγ t).continuousAt`. Use `intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => (hγ t).clog_real (hs t ht)) ?_` and prove the remaining obligations. Use `ContinuousOn.intervalIntegrable ?_` and prove the remaining obligations. Conclude with `continuousOn_const.div hc.continuousOn fun t ht => Complex.slitPlane_ne_zero (hs t ht)`.
-/
theorem rectRes_ftc_log {γ : ℝ → ℂ} {d : ℂ} {a b : ℝ} (hγ : ∀ t, HasDerivAt γ d t)
    (hs : ∀ t ∈ Set.uIcc a b, γ t ∈ slitPlane) :
    ∫ t in a..b, d / γ t = log (γ b) - log (γ a) := by
  have hc : Continuous γ := continuous_iff_continuousAt.2 fun t => (hγ t).continuousAt
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => (hγ t).clog_real (hs t ht)) ?_
  refine ContinuousOn.intervalIntegrable ?_
  exact continuousOn_const.div hc.continuousOn fun t ht => Complex.slitPlane_ne_zero (hs t ht)

/- English proof (translation)
Establish `h1` using `Complex.arg_neg_eq_arg_sub_pi_of_im_pos h`. Apply the tactic sequence `apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]`.
-/
theorem rectRes_log_sub_log_neg_of_im_pos {z : ℂ} (h : 0 < z.im) :
    log z - log (-z) = (Real.pi : ℂ) * I := by
  have h1 := Complex.arg_neg_eq_arg_sub_pi_of_im_pos h
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]

/- English proof (translation)
Establish `h1` using `Complex.arg_neg_eq_arg_add_pi_of_im_neg h`. Apply the tactic sequence `apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]`.
-/
theorem rectRes_log_sub_log_neg_of_im_neg {z : ℂ} (h : z.im < 0) :
    log z - log (-z) = -((Real.pi : ℂ) * I) := by
  have h1 := Complex.arg_neg_eq_arg_add_pi_of_im_neg h
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]

/- English proof (translation)
Establish `h` using `(Complex.ofRealCLM.hasDerivAt (x := t)).add_const c`. Simplify using `using h`.
-/
theorem rectRes_hasDerivAt_horiz (c : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) + c) 1 t := by
  have h := (Complex.ofRealCLM.hasDerivAt (x := t)).add_const c
  simpa using h

/- English proof (translation)
Establish `h` using `((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add c`. Simplify using `using h`.
-/
theorem rectRes_hasDerivAt_vert (c : ℂ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => c + (y : ℂ) * I) I t := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add c
  simpa using h

/- English proof (translation)
Establish `E1 : ∫ x in x0..x1, 1 / ((x : ℂ) + (y0 : ℂ) * I - p) = log ((x1 : ℂ) + (y0 : ℂ) * I - p) - log ((x0 : ℂ) + (y0 : ℂ) * I - p)`. Establish `h` using `rectRes_ftc_log (γ := fun x : ℝ => (x : ℂ) + ((y0 : ℂ) * I - p)) (d := 1) (a := x0) (b := x1) (fun t => rectRes_hasDerivAt_horiz _ t) (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inr (by intro h'; simp at h'; linarith)))`. Simplify `h` using `only [add_sub_assoc]`. Establish `E2 : ∫ x in x0..x1, 1 / ((x : ℂ) + (y1 : ℂ) * I - p) = log ((x1 : ℂ) + (y1 : ℂ) * I - p) - log ((x0 : ℂ) + (y1 : ℂ) * I - p)`. Establish `h` using `rectRes_ftc_log (γ := fun x : ℝ => (x : ℂ) + ((y1 : ℂ) * I - p)) (d := 1) (a := x0) (b := x1) (fun t => rectRes_hasDerivAt_horiz _ t) (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inr (by intro h'; simp at h'; linarith)))`.

Simplify `h` using `only [add_sub_assoc]`. Establish `E3 : I * ∫ y in y0..y1, 1 / ((x1 : ℂ) + (y : ℂ) * I - p) = log ((x1 : ℂ) + (y1 : ℂ) * I - p) - log ((x1 : ℂ) + (y0 : ℂ) * I - p)`. Apply the tactic sequence `have h := rectRes_ftc_log (γ := fun y : ℝ => ((x1 : ℂ) - p) + (y : ℂ) * I) (d := I) (a := y0) (b := y1) (fun t => rectRes_hasDerivAt_vert _ t) (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inl (by simp <;> linarith)))`. Rewrite using `[← intervalIntegral.integral_const_mul]`. Establish `e1 : (x1 : ℂ) + (y1 : ℂ) * I - p = ((x1 : ℂ) - p) + (y1 : ℂ) * I` using `by ring`.

Establish `e0 : (x1 : ℂ) + (y0 : ℂ) * I - p = ((x1 : ℂ) - p) + (y0 : ℂ) * I` using `by ring`. Rewrite using `[e1, e0, ← h]`. Use `intervalIntegral.integral_congr (fun y _ => ?_)` and prove the remaining obligations. Use `show I * (1 / ((x1 : ℂ) + (y : ℂ) * I - p)) = I / (((x1 : ℂ) - p) + (y : ℂ) * I)`. Rewrite using `[mul_one_div]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `E4 : I * ∫ y in y0..y1, 1 / ((x0 : ℂ) + (y : ℂ) * I - p) = log (-((x0 : ℂ) + (y1 : ℂ) * I - p)) - log (-((x0 : ℂ) + (y0 : ℂ) * I - p))`. Apply the tactic sequence `have h := rectRes_ftc_log (γ := fun y : ℝ => -(((x0 : ℂ) - p) + (y : ℂ) * I)) (d := -I) (a := y0) (b := y1) (fun t => (rectRes_hasDerivAt_vert _ t).neg) (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inl (by simp <;> linarith)))`. Rewrite using `[← intervalIntegral.integral_const_mul]`.

Establish `e1 : (x0 : ℂ) + (y1 : ℂ) * I - p = ((x0 : ℂ) - p) + (y1 : ℂ) * I` using `by ring`. Establish `e0 : (x0 : ℂ) + (y0 : ℂ) * I - p = ((x0 : ℂ) - p) + (y0 : ℂ) * I` using `by ring`. Rewrite using `[e1, e0, ← h]`. Use `intervalIntegral.integral_congr (fun y _ => ?_)` and prove the remaining obligations. Use `show I * (1 / ((x0 : ℂ) + (y : ℂ) * I - p)) = -I / -(((x0 : ℂ) - p) + (y : ℂ) * I)`.

Rewrite using `[neg_div_neg_eq, mul_one_div]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `have P1 := rectRes_log_sub_log_neg_of_im_pos (z := (x0 : ℂ) + (y1 : ℂ) * I - p) (by simp <;> linarith)`. Apply the tactic sequence `have P0 := rectRes_log_sub_log_neg_of_im_neg (z := (x0 : ℂ) + (y0 : ℂ) * I - p) (by simp <;> linarith)`.

Unfold `rectInt`. Use `beta_reduce`. Rewrite using `[E1, E2, E3, E4]`. Take the linear combination `P1 - P0`.
-/
theorem rectInt_inv_sub (p : ℂ) (x0 x1 y0 y1 : ℝ) (h1 : x0 < p.re) (h2 : p.re < x1)
    (h3 : y0 < p.im) (h4 : p.im < y1) :
    rectInt (fun w => 1 / (w - p)) x0 x1 y0 y1 = 2 * (Real.pi : ℂ) * I := by
  have E1 : ∫ x in x0..x1, 1 / ((x : ℂ) + (y0 : ℂ) * I - p) =
      log ((x1 : ℂ) + (y0 : ℂ) * I - p) - log ((x0 : ℂ) + (y0 : ℂ) * I - p) := by
    have h := rectRes_ftc_log (γ := fun x : ℝ => (x : ℂ) + ((y0 : ℂ) * I - p)) (d := 1)
      (a := x0) (b := x1) (fun t => rectRes_hasDerivAt_horiz _ t)
      (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inr (by intro h'; simp at h'; linarith)))
    simpa only [add_sub_assoc] using h
  have E2 : ∫ x in x0..x1, 1 / ((x : ℂ) + (y1 : ℂ) * I - p) =
      log ((x1 : ℂ) + (y1 : ℂ) * I - p) - log ((x0 : ℂ) + (y1 : ℂ) * I - p) := by
    have h := rectRes_ftc_log (γ := fun x : ℝ => (x : ℂ) + ((y1 : ℂ) * I - p)) (d := 1)
      (a := x0) (b := x1) (fun t => rectRes_hasDerivAt_horiz _ t)
      (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inr (by intro h'; simp at h'; linarith)))
    simpa only [add_sub_assoc] using h
  have E3 : I * ∫ y in y0..y1, 1 / ((x1 : ℂ) + (y : ℂ) * I - p) =
      log ((x1 : ℂ) + (y1 : ℂ) * I - p) - log ((x1 : ℂ) + (y0 : ℂ) * I - p) := by
    have h := rectRes_ftc_log (γ := fun y : ℝ => ((x1 : ℂ) - p) + (y : ℂ) * I) (d := I)
      (a := y0) (b := y1) (fun t => rectRes_hasDerivAt_vert _ t)
      (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inl (by simp <;> linarith)))
    rw [← intervalIntegral.integral_const_mul]
    have e1 : (x1 : ℂ) + (y1 : ℂ) * I - p = ((x1 : ℂ) - p) + (y1 : ℂ) * I := by ring
    have e0 : (x1 : ℂ) + (y0 : ℂ) * I - p = ((x1 : ℂ) - p) + (y0 : ℂ) * I := by ring
    rw [e1, e0, ← h]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    show I * (1 / ((x1 : ℂ) + (y : ℂ) * I - p)) = I / (((x1 : ℂ) - p) + (y : ℂ) * I)
    rw [mul_one_div]
    congr 1
    ring
  have E4 : I * ∫ y in y0..y1, 1 / ((x0 : ℂ) + (y : ℂ) * I - p) =
      log (-((x0 : ℂ) + (y1 : ℂ) * I - p)) - log (-((x0 : ℂ) + (y0 : ℂ) * I - p)) := by
    have h := rectRes_ftc_log (γ := fun y : ℝ => -(((x0 : ℂ) - p) + (y : ℂ) * I)) (d := -I)
      (a := y0) (b := y1) (fun t => (rectRes_hasDerivAt_vert _ t).neg)
      (fun t _ => Complex.mem_slitPlane_iff.2 (Or.inl (by simp <;> linarith)))
    rw [← intervalIntegral.integral_const_mul]
    have e1 : (x0 : ℂ) + (y1 : ℂ) * I - p = ((x0 : ℂ) - p) + (y1 : ℂ) * I := by ring
    have e0 : (x0 : ℂ) + (y0 : ℂ) * I - p = ((x0 : ℂ) - p) + (y0 : ℂ) * I := by ring
    rw [e1, e0, ← h]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    show I * (1 / ((x0 : ℂ) + (y : ℂ) * I - p)) = -I / -(((x0 : ℂ) - p) + (y : ℂ) * I)
    rw [neg_div_neg_eq, mul_one_div]
    congr 1
    ring
  have P1 := rectRes_log_sub_log_neg_of_im_pos (z := (x0 : ℂ) + (y1 : ℂ) * I - p)
    (by simp <;> linarith)
  have P0 := rectRes_log_sub_log_neg_of_im_neg (z := (x0 : ℂ) + (y0 : ℂ) * I - p)
    (by simp <;> linarith)
  unfold rectInt
  beta_reduce
  rw [E1, E2, E3, E4]
  linear_combination P1 - P0

/- English proof (translation)
Establish `hγP : ∀ t ∈ Set.uIcc a c, γ t ∉ P` using `fun t ht hmem => hP t ht _ hmem rfl`. Establish `hcont : ∀ p ∈ P, ContinuousOn (fun t => 1 / (γ t - p)) (Set.uIcc a c)` using `fun p hp => continuousOn_const.div (hγ.continuousOn.sub continuousOn_const) (fun t ht => sub_ne_zero.2 (hP t ht p hp))`. Combine the equalities or inequalities in the displayed calculation. Use `intervalIntegral.integral_congr (fun t ht => ?_)` and prove the remaining obligations. Use `show g (γ t) = G (γ t) + ∑ p ∈ P, b p * (1 / (γ t - p))`.

Rewrite using `[hg _ (hγP t ht)]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations. Rewrite using `[mul_one_div]`. Use `_ = (∫ t in a..c, G (γ t)) + ∫ t in a..c, ∑ p ∈ P, b p * (1 / (γ t - p)) := by`.

Use `intervalIntegral.integral_add hG.intervalIntegrable ?_` and prove the remaining obligations. Conclude with `(continuousOn_finset_sum P (fun p hp => continuousOn_const.mul (hcont p hp))).intervalIntegrable`. Use `_ = (∫ t in a..c, G (γ t)) + ∑ p ∈ P, b p * ∫ t in a..c, 1 / (γ t - p) := by`. Rewrite using `[intervalIntegral.integral_finset_sum]`. Repeatedly rewrite using `[intervalIntegral.integral_const_mul]`.

Introduce `p hp`. Conclude with `((hcont p hp).intervalIntegrable).const_mul (b p)`.
-/
theorem rectRes_edge (g G : ℂ → ℂ) (P : Finset ℂ) (b : ℂ → ℂ) (γ : ℝ → ℂ) (a c : ℝ)
    (hγ : Continuous γ) (hG : ContinuousOn (fun t => G (γ t)) (Set.uIcc a c))
    (hP : ∀ t ∈ Set.uIcc a c, ∀ p ∈ P, γ t ≠ p)
    (hg : ∀ w : ℂ, w ∉ P → g w = G w + ∑ p ∈ P, b p / (w - p)) :
    ∫ t in a..c, g (γ t) =
      (∫ t in a..c, G (γ t)) + ∑ p ∈ P, b p * ∫ t in a..c, 1 / (γ t - p) := by
  have hγP : ∀ t ∈ Set.uIcc a c, γ t ∉ P := fun t ht hmem => hP t ht _ hmem rfl
  have hcont : ∀ p ∈ P, ContinuousOn (fun t => 1 / (γ t - p)) (Set.uIcc a c) := fun p hp =>
    continuousOn_const.div (hγ.continuousOn.sub continuousOn_const)
      (fun t ht => sub_ne_zero.2 (hP t ht p hp))
  calc ∫ t in a..c, g (γ t)
      = ∫ t in a..c, (G (γ t) + ∑ p ∈ P, b p * (1 / (γ t - p))) := by
        refine intervalIntegral.integral_congr (fun t ht => ?_)
        show g (γ t) = G (γ t) + ∑ p ∈ P, b p * (1 / (γ t - p))
        rw [hg _ (hγP t ht)]
        congr 1
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [mul_one_div]
    _ = (∫ t in a..c, G (γ t)) + ∫ t in a..c, ∑ p ∈ P, b p * (1 / (γ t - p)) := by
        refine intervalIntegral.integral_add hG.intervalIntegrable ?_
        exact (continuousOn_finset_sum P (fun p hp => continuousOn_const.mul (hcont p hp))).intervalIntegrable
    _ = (∫ t in a..c, G (γ t)) + ∑ p ∈ P, b p * ∫ t in a..c, 1 / (γ t - p) := by
        rw [intervalIntegral.integral_finset_sum]
        · simp_rw [intervalIntegral.integral_const_mul]
        · intro p hp
          exact ((hcont p hp).intervalIntegrable).const_mul (b p)

/- English proof (translation)
Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun p _ => by ring`.
-/
theorem rectRes_sum_combo (P : Finset ℂ) (b A B C D : ℂ → ℂ) :
    ∑ p ∈ P, b p * (A p - B p + I * C p - I * D p) =
      ∑ p ∈ P, b p * A p - ∑ p ∈ P, b p * B p + I * ∑ p ∈ P, b p * C p - I * ∑ p ∈ P, b p * D p := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

/- English proof (translation)
Unfold `RectResidue`. Introduce `g G P b x0 x1 y0 y1 _ _ hPin hU hg`. Take `⟨U, -, hsub, hGd⟩` from `hU`. Establish `hGc : ContinuousOn G U` using `hGd.continuousOn`. Establish `hG0 : ((∫ x in x0..x1, G ((x : ℂ) + (y0 : ℂ) * I)) - (∫ x in x0..x1, G ((x : ℂ) + (y1 : ℂ) * I)) + I * (∫ y in y0..y1, G ((x1 : ℂ) + (y : ℂ) * I))) - I * (∫ y in y0..y1, G ((x0 : ℂ) + (y : ℂ) * I)) = 0`.

Establish `h` using `Complex.integral_boundary_rect_eq_zero_of_differentiableOn G ⟨x0, y0⟩ ⟨x1, y1⟩ (hGd.mono hsub)`. Simplify using `only [smul_eq_mul] at h`. Conclude with `h`. Establish `eB` using `rectRes_edge g G P b (fun x : ℝ => (x : ℂ) + (y0 : ℂ) * I) x0 x1 (Complex.continuous_ofReal.add continuous_const) (hGc.comp (Complex.continuous_ofReal.add continuous_const).continuousOn (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simpa using ht, by simp⟩))) (fun t _ p hp h => b …`. Establish `h'` using `congrArg Complex.im h`.

Simplify using `at h'`. Combine the linear relations using `[(hPin p hp).2.2.1]) hg`. Establish `eT` using `rectRes_edge g G P b (fun x : ℝ => (x : ℂ) + (y1 : ℂ) * I) x0 x1 (Complex.continuous_ofReal.add continuous_const) (hGc.comp (Complex.continuous_ofReal.add continuous_const).continuousOn (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simpa using ht, by simp⟩))) (fun t _ p hp h => b …`. Establish `h'` using `congrArg Complex.im h`. Simplify using `at h'`.

Combine the linear relations using `[(hPin p hp).2.2.2]) hg`. Establish `eR` using `rectRes_edge g G P b (fun y : ℝ => (x1 : ℂ) + (y : ℂ) * I) y0 y1 (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) (hGc.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by si …`. Establish `h'` using `congrArg Complex.re h`. Simplify using `at h'`. Combine the linear relations using `[(hPin p hp).2.1]) hg`.

Establish `eL` using `rectRes_edge g G P b (fun y : ℝ => (x0 : ℂ) + (y : ℂ) * I) y0 y1 (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) (hGc.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by si …`. Establish `h'` using `congrArg Complex.re h`. Simplify using `at h'`. Combine the linear relations using `[(hPin p hp).1]) hg`. Establish `hc` using `rectRes_sum_combo P b (fun p => ∫ t in x0..x1, 1 / ((t : ℂ) + (y0 : ℂ) * I - p)) (fun p => ∫ t in x0..x1, 1 / ((t : ℂ) + (y1 : ℂ) * I - p)) (fun p => ∫ t in y0..y1, 1 / ((x1 : ℂ) + (t : ℂ) * I - p)) (fun p => ∫ t in y0..y1, 1 / ((x0 : ℂ) + (t : ℂ) * I - p))`.

Establish `hsum : ∑ p ∈ P, b p * ((∫ t in x0..x1, 1 / ((t : ℂ) + (y0 : ℂ) * I - p)) - (∫ t in x0..x1, 1 / ((t : ℂ) + (y1 : ℂ) * I - p)) + I * (∫ t in y0..y1, 1 / ((x1 : ℂ) + (t : ℂ) * I - p)) - I * (∫ t in y0..y1, 1 / ((x0 : ℂ) + (t : ℂ) * I - p))) = 2 * (Real.pi : ℂ) * I * ∑ p ∈ P, b p`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun p hp => ?_)` and prove the remaining obligations. Establish `h` using `rectInt_inv_sub p x0 x1 y0 y1 (hPin p hp).1 (hPin p hp).2.1 (hPin p hp).2.2.1 (hPin p hp).2.2.2`. Unfold `rectInt at h`.

Use `beta_reduce at h`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Unfold `rectInt`. Take the linear combination `eB - eT + I * eR - I * eL + hG0 + hsum - hc`.
-/
theorem rectangle_residue : RectResidue := by
  unfold RectResidue
  intro g G P b x0 x1 y0 y1 _ _ hPin hU hg
  obtain ⟨U, -, hsub, hGd⟩ := hU
  have hGc : ContinuousOn G U := hGd.continuousOn
  have hG0 : ((∫ x in x0..x1, G ((x : ℂ) + (y0 : ℂ) * I)) - (∫ x in x0..x1, G ((x : ℂ) + (y1 : ℂ) * I))
      + I * (∫ y in y0..y1, G ((x1 : ℂ) + (y : ℂ) * I))) - I * (∫ y in y0..y1, G ((x0 : ℂ) + (y : ℂ) * I))
      = 0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G ⟨x0, y0⟩ ⟨x1, y1⟩
      (hGd.mono hsub)
    simp only [smul_eq_mul] at h
    exact h
  have eB := rectRes_edge g G P b (fun x : ℝ => (x : ℂ) + (y0 : ℂ) * I) x0 x1
    (Complex.continuous_ofReal.add continuous_const)
    (hGc.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
      (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simpa using ht, by simp⟩)))
    (fun t _ p hp h => by
      have h' := congrArg Complex.im h
      simp at h'
      linarith [(hPin p hp).2.2.1]) hg
  have eT := rectRes_edge g G P b (fun x : ℝ => (x : ℂ) + (y1 : ℂ) * I) x0 x1
    (Complex.continuous_ofReal.add continuous_const)
    (hGc.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
      (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simpa using ht, by simp⟩)))
    (fun t _ p hp h => by
      have h' := congrArg Complex.im h
      simp at h'
      linarith [(hPin p hp).2.2.2]) hg
  have eR := rectRes_edge g G P b (fun y : ℝ => (x1 : ℂ) + (y : ℂ) * I) y0 y1
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    (hGc.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simp, by simpa using ht⟩)))
    (fun t _ p hp h => by
      have h' := congrArg Complex.re h
      simp at h'
      linarith [(hPin p hp).2.1]) hg
  have eL := rectRes_edge g G P b (fun y : ℝ => (x0 : ℂ) + (y : ℂ) * I) y0 y1
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    (hGc.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simp, by simpa using ht⟩)))
    (fun t _ p hp h => by
      have h' := congrArg Complex.re h
      simp at h'
      linarith [(hPin p hp).1]) hg
  have hc := rectRes_sum_combo P b
    (fun p => ∫ t in x0..x1, 1 / ((t : ℂ) + (y0 : ℂ) * I - p))
    (fun p => ∫ t in x0..x1, 1 / ((t : ℂ) + (y1 : ℂ) * I - p))
    (fun p => ∫ t in y0..y1, 1 / ((x1 : ℂ) + (t : ℂ) * I - p))
    (fun p => ∫ t in y0..y1, 1 / ((x0 : ℂ) + (t : ℂ) * I - p))
  have hsum : ∑ p ∈ P, b p * ((∫ t in x0..x1, 1 / ((t : ℂ) + (y0 : ℂ) * I - p))
      - (∫ t in x0..x1, 1 / ((t : ℂ) + (y1 : ℂ) * I - p))
      + I * (∫ t in y0..y1, 1 / ((x1 : ℂ) + (t : ℂ) * I - p))
      - I * (∫ t in y0..y1, 1 / ((x0 : ℂ) + (t : ℂ) * I - p)))
      = 2 * (Real.pi : ℂ) * I * ∑ p ∈ P, b p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have h := rectInt_inv_sub p x0 x1 y0 y1 (hPin p hp).1 (hPin p hp).2.1 (hPin p hp).2.2.1
      (hPin p hp).2.2.2
    unfold rectInt at h
    beta_reduce at h
    rw [h]
    ring
  unfold rectInt
  linear_combination eB - eT + I * eR - I * eL + hG0 + hsum - hc

end Formalism.FX
