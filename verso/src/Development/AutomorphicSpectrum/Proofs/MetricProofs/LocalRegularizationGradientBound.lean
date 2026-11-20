import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

/- English proof (translation)
Establish `h` using `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a (1 / 6 : ℝ) (by norm_num)`. Establish `h2 : Tendsto (fun y : ℝ => (c * Real.exp (K' / 6)) * (y ^ a * Real.exp (-(1 / 6) * y))) atTop (nhds 0)`. Simplify `h.const_mul (c * Real.exp (K' / 6))` using `[neg_mul]`. Establish `h3` using `h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))`. Take `⟨Y, hY⟩` from `eventually_atTop.1 h3`.

Use `⟨Real.exp (K' - Y), Real.exp_pos _, fun t ht htle => ?_⟩` and prove the remaining obligations. Use `set y := Real.log (1 / t) + K' with hy`. Establish `hlog : Real.log t = K' - y`. Rewrite using `[hy, one_div, Real.log_inv]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hYy : Y ≤ y`. Use `Real.log_le_log ht htle` as an intermediate fact. Rewrite `this` using `[Real.log_exp, hlog]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs` using `(hY y hYy).le`.

Establish `e1 : t ^ ((1 : ℝ) / 2) = t ^ ((1 : ℝ) / 3) * (Real.exp (K' / 6) * Real.exp (-(1 / 6) * y))`. Establish `: Real.exp (K' / 6) * Real.exp (-(1 / 6) * y) = t ^ ((1 : ℝ) / 6)`. Rewrite using `[← Real.exp_add, Real.rpow_def_of_pos ht, hlog]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, ← Real.rpow_add ht]`. Evaluate the numerical expressions. Establish `hp : 0 < t ^ ((1 : ℝ) / 3)` using `Real.rpow_pos_of_pos ht _`. Rewrite using `[e1]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma near_small (a c K' : ℝ) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ t, 0 < t → t ≤ t₁ →
      c * (Real.log (1 / t) + K') ^ a * t ^ ((1 : ℝ) / 2) ≤ t ^ ((1 : ℝ) / 3) / 2 := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a (1 / 6 : ℝ) (by norm_num)
  have h2 : Tendsto (fun y : ℝ => (c * Real.exp (K' / 6)) * (y ^ a * Real.exp (-(1 / 6) * y)))
      atTop (nhds 0) := by
    simpa [neg_mul] using h.const_mul (c * Real.exp (K' / 6))
  have h3 := h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨Y, hY⟩ := eventually_atTop.1 h3
  refine ⟨Real.exp (K' - Y), Real.exp_pos _, fun t ht htle => ?_⟩
  set y := Real.log (1 / t) + K' with hy
  have hlog : Real.log t = K' - y := by
    rw [hy, one_div, Real.log_inv]; ring
  have hYy : Y ≤ y := by
    have := Real.log_le_log ht htle
    rw [Real.log_exp, hlog] at this
    linarith
  have hs := (hY y hYy).le
  have e1 : t ^ ((1 : ℝ) / 2) =
      t ^ ((1 : ℝ) / 3) * (Real.exp (K' / 6) * Real.exp (-(1 / 6) * y)) := by
    have : Real.exp (K' / 6) * Real.exp (-(1 / 6) * y) = t ^ ((1 : ℝ) / 6) := by
      rw [← Real.exp_add, Real.rpow_def_of_pos ht, hlog]; congr 1; ring
    rw [this, ← Real.rpow_add ht]; norm_num
  have hp : 0 < t ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos ht _
  rw [e1]
  calc c * y ^ a * (t ^ ((1 : ℝ) / 3) * (Real.exp (K' / 6) * Real.exp (-(1 / 6) * y)))
      = t ^ ((1 : ℝ) / 3) * (c * Real.exp (K' / 6) * (y ^ a * Real.exp (-(1 / 6) * y))) := by ring
    _ ≤ t ^ ((1 : ℝ) / 3) * (1 / 2) := mul_le_mul_of_nonneg_left hs hp.le
    _ = t ^ ((1 : ℝ) / 3) / 2 := by ring

/- English proof (translation)
Introduce `D S m u C₅ K hm hd hg`. Establish `hclosed : IsClosed (ReciprocityTheory.AnForm.A.coordDiv S)`. Establish `: ReciprocityTheory.AnForm.A.coordDiv S = ⋃ i ∈ S, {z : Fin D → ℂ | z i = 0}`. Use extensionality with `z`. Simplify using `[ReciprocityTheory.AnForm.A.coordDiv]`.

Rewrite using `[this]`. Conclude with `S.finite_toSet.isClosed_biUnion (fun i _ => isClosed_eq (continuous_apply i) continuous_const)`. Establish `hopen : IsOpen (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S)` using `isOpen_ball.sdiff hclosed`. Use `set a := |C₅| with ha`. Use `set K' := K + RegularChartScaling.mTot S m * Real.log 4 with hK'`.

Take `⟨t₁, ht₁, hsm⟩` from `near_small a (a * Real.exp (K' / 2)) K'`. Use `⟨min (min (1 / 4) (Real.exp (-K))) t₁, by positivity, fun t ht htle z hz hr => ?_⟩` and prove the remaining obligations. Establish `ht4 : t ≤ 1 / 4` using `htle.trans ((min_le_left _ _).trans (min_le_left _ _))`. Establish `htK : t ≤ Real.exp (-K)` using `htle.trans ((min_le_left _ _).trans (min_le_right _ _))`. Establish `ht1 : t ≤ t₁` using `htle.trans (min_le_right _ _)`.

Take `⟨hzB, hzD⟩` from `hz`. Establish `hzn : ∀ i, ‖z i‖ ≤ 2` using `RegularChartScaling.norm_coord_le_of_ball (by norm_num : (5 / 4 : ℝ) ≤ 2) hzB`. Establish `hzi : ∀ i ∈ S, z i ≠ 0` using `fun i hi h0 => hzD ⟨i, hi, h0⟩`. Establish `hcoord : ∀ i ∈ S, 2 * t ≤ ‖z i‖`. Introduce `i hi`.

Establish `hpos : 0 < ‖z i‖` using `norm_pos_iff.2 (hzi i hi)`. Establish `hterm : Real.log (4 / ‖z i‖ ^ 2) ≤ Real.log (1 / t) + K`. Establish `h1 : (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2) ≤ ∑ j ∈ S, (m j : ℝ) * Real.log (4 / ‖z j‖ ^ 2)` using `Finset.single_le_sum (f := fun j => (m j : ℝ) * Real.log (4 / ‖z j‖ ^ 2)) (fun j _ => mul_nonneg (Nat.cast_nonneg _) (RegularChartScaling.log_term_nonneg (hzn j))) hi`. Establish `h2 : Real.log (4 / ‖z i‖ ^ 2) ≤ (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2)` using `le_mul_of_one_le_left (RegularChartScaling.log_term_nonneg (hzn i)) (by exact_mod_cast hm i hi)`. Establish `h3` using `Real.exp_pos 1`.

Unfold `rLoc at hr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hEK : Real.exp K ≤ 1 / t`. Rewrite `htK` using `[Real.exp_neg]`. Rewrite using `[le_div_iff₀ ht]`.

Use `mul_le_mul_of_nonneg_left htK (Real.exp_pos K).le` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ (Real.exp_pos K).ne']`. Then use the resulting hypothesis. Establish `hE : Real.exp (Real.log (1 / t) + K) ≤ 1 / t ^ 2`. Rewrite using `[Real.exp_add, Real.exp_log (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h4 : 4 / ‖z i‖ ^ 2 ≤ 1 / t ^ 2` using `((Real.log_le_iff_le_exp (by positivity)).1 hterm).trans hE`. Rewrite `h4` using `[div_le_div_iff₀ (by positivity) (by positivity)]`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Use the polynomial consequences of the given equalities and inequalities.

Use `set y := Real.log (1 / t) + K' with hy`. Establish `hfar : ∀ x ∈ closedBall z t, ∀ i ∈ S, ‖z i‖ / 2 ≤ ‖x i‖ ∧ 0 < ‖x i‖`. Introduce `x hx i hi`. Establish `h1 : ‖x i - z i‖ ≤ t` using `(norm_le_pi_norm (x - z) i).trans (mem_closedBall_iff_norm.1 hx)`. Establish `h2` using `norm_sub_norm_le (z i) (x i)`.

Rewrite `h2` using `[norm_sub_rev]`. Establish `h3` using `hcoord i hi`. Apply the tactic sequence `constructor <;> linarith`. Establish `hmem : ∀ x ∈ closedBall z t, x ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S`. Introduce `x hx`.

Use `⟨RegularChartScaling.closedBall_sub_of hzB (by linarith) hx, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨i, hi, h0⟩`. Use `(hfar x hx i hi).2` as an intermediate fact. Rewrite `this` using `[h0, norm_zero]`. Conclude with `lt_irrefl _ this`.

Establish `hrx : ∀ x ∈ closedBall z t, rLoc S m x ≤ y`. Introduce `x hx`. Establish `key : ∀ i ∈ S, (m i : ℝ) * Real.log (4 / ‖x i‖ ^ 2) ≤ (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2) + (m i : ℝ) * Real.log 4`. Introduce `i hi`. Take `⟨h1, h2⟩` from `hfar x hx i hi`.

Establish `hzp : 0 < ‖z i‖` using `norm_pos_iff.2 (hzi i hi)`. Rewrite using `[← mul_add]`. Use `mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)` and prove the remaining obligations. Rewrite using `[← Real.log_mul (by positivity) (by norm_num)]`. Use `Real.log_le_log (by positivity) ?_` and prove the remaining obligations.

Rewrite using `[div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]`. Use polynomial arithmetic with `[mul_self_le_mul_self (by positivity) h1]`. Establish `hsum` using `Finset.sum_le_sum key`. Rewrite `hsum` using `[Finset.sum_add_distrib, ← Finset.sum_mul]`. Unfold `rLoc at hr ⊢`.

Simplify using `only [hy, hK', RegularChartScaling.mTot]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set B := a * y ^ a * Real.exp (y / 2) with hB`. Establish `hfd : ∀ x ∈ closedBall z t, ‖fderiv ℝ u x‖ ≤ B`. Introduce `x hx`.

Establish `hxm` using `hmem x hx`. Establish `hxn : ∀ i, ‖x i‖ ≤ 2` using `RegularChartScaling.norm_coord_le_of_ball (by norm_num : (3 / 2 : ℝ) ≤ 2) hxm.1`. Establish `hr1 : 1 ≤ rLoc S m x`. Use `RegularChartScaling.rLoc_ge S m hxn` as an intermediate fact. Combine the linear relations using `[Real.add_one_le_exp (1 : ℝ)]`.

Establish `hry` using `hrx x hx`. Establish `hy0 : 0 ≤ y` using `by linarith`. Establish `hp : rLoc S m x ^ C₅ ≤ y ^ a` using `(Real.rpow_le_rpow_of_exponent_le hr1 (le_abs_self C₅)).trans (Real.rpow_le_rpow (by linarith) hry (abs_nonneg _))`. Use `(hg x hxm).trans ?_` and prove the remaining obligations. Use `mul_le_mul (mul_le_mul (le_abs_self C₅) hp (Real.rpow_nonneg (by linarith) _) (abs_nonneg _)) (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hy0 _))` and prove the remaining obligations.

Establish `hB0 : 0 ≤ B` using `(norm_nonneg _).trans (hfd z (mem_closedBall_self ht.le))`. Establish `hBt : B * t ≤ t ^ ((1 : ℝ) / 3) / 2`. Establish `hlog : Real.log t = K' - y`. Rewrite using `[hy, one_div, Real.log_inv]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e : Real.exp (y / 2) * t = Real.exp (K' / 2) * t ^ ((1 : ℝ) / 2)`. Rewrite using `[Real.rpow_def_of_pos ht, hlog]`. Use `nth_rewrite 1 [← Real.exp_log ht]`. Rewrite using `[hlog, ← Real.exp_add, ← Real.exp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Unfold `polyMaxOff`. Use `csSup_le ⟨u z, z, ⟨mem_closedBall_self ht.le, hzD⟩, rfl⟩ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, ⟨hx, -⟩, rfl⟩`.

Establish `hmv` using `Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := u) (s := closedBall z t) (x := z) (y := x) (C := B) (fun w hw => (hd w (hmem w hw)).differentiableAt (hopen.mem_nhds (hmem w hw))) hfd (convex_closedBall z t) (mem_closedBall_self ht.le) hx`. Establish `h1 : ‖x - z‖ ≤ t` using `mem_closedBall_iff_norm.1 hx`. Establish `h2 : u x - u z ≤ ‖u x - u z‖` using `Real.le_norm_self _`. Establish `h3 : B * ‖x - z‖ ≤ B * t` using `mul_le_mul_of_nonneg_left h1 hB0`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem polyMaxOff_le_of_rLoc_le :
    ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (u : (Fin D → ℂ) → ℝ) (C₅ K : ℝ), (∀ i ∈ S, 1 ≤ m i) → DifferentiableOn ℝ u (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, ‖fderiv ℝ u z‖ ≤ C₅ * rLoc S m z ^ C₅ * Real.exp (rLoc S m z / 2)) → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t, 0 < t → t ≤ t₀ → ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, rLoc S m z ≤ Real.log (1 / t) + K → polyMaxOff S u z t ≤ u z + t ^ ((1 : ℝ) / 3) / 2 := by
  intro D S m u C₅ K hm hd hg
  have hclosed : IsClosed (ReciprocityTheory.AnForm.A.coordDiv S) := by
    have : ReciprocityTheory.AnForm.A.coordDiv S = ⋃ i ∈ S, {z : Fin D → ℂ | z i = 0} := by
      ext z; simp [ReciprocityTheory.AnForm.A.coordDiv]
    rw [this]
    exact S.finite_toSet.isClosed_biUnion
      (fun i _ => isClosed_eq (continuous_apply i) continuous_const)
  have hopen : IsOpen (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) :=
    isOpen_ball.sdiff hclosed
  set a := |C₅| with ha
  set K' := K + RegularChartScaling.mTot S m * Real.log 4 with hK'
  obtain ⟨t₁, ht₁, hsm⟩ := near_small a (a * Real.exp (K' / 2)) K'
  refine ⟨min (min (1 / 4) (Real.exp (-K))) t₁, by positivity, fun t ht htle z hz hr => ?_⟩
  have ht4 : t ≤ 1 / 4 := htle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have htK : t ≤ Real.exp (-K) := htle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have ht1 : t ≤ t₁ := htle.trans (min_le_right _ _)
  obtain ⟨hzB, hzD⟩ := hz
  have hzn : ∀ i, ‖z i‖ ≤ 2 :=
    RegularChartScaling.norm_coord_le_of_ball (by norm_num : (5 / 4 : ℝ) ≤ 2) hzB
  have hzi : ∀ i ∈ S, z i ≠ 0 := fun i hi h0 => hzD ⟨i, hi, h0⟩
  have hcoord : ∀ i ∈ S, 2 * t ≤ ‖z i‖ := by
    intro i hi
    have hpos : 0 < ‖z i‖ := norm_pos_iff.2 (hzi i hi)
    have hterm : Real.log (4 / ‖z i‖ ^ 2) ≤ Real.log (1 / t) + K := by
      have h1 : (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2) ≤
          ∑ j ∈ S, (m j : ℝ) * Real.log (4 / ‖z j‖ ^ 2) :=
        Finset.single_le_sum (f := fun j => (m j : ℝ) * Real.log (4 / ‖z j‖ ^ 2))
          (fun j _ => mul_nonneg (Nat.cast_nonneg _) (RegularChartScaling.log_term_nonneg (hzn j))) hi
      have h2 : Real.log (4 / ‖z i‖ ^ 2) ≤ (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2) :=
        le_mul_of_one_le_left (RegularChartScaling.log_term_nonneg (hzn i)) (by exact_mod_cast hm i hi)
      have h3 := Real.exp_pos 1
      unfold rLoc at hr
      linarith
    have hEK : Real.exp K ≤ 1 / t := by
      rw [Real.exp_neg] at htK
      rw [le_div_iff₀ ht]
      have := mul_le_mul_of_nonneg_left htK (Real.exp_pos K).le
      rwa [mul_inv_cancel₀ (Real.exp_pos K).ne'] at this
    have hE : Real.exp (Real.log (1 / t) + K) ≤ 1 / t ^ 2 := by
      rw [Real.exp_add, Real.exp_log (by positivity)]
      calc 1 / t * Real.exp K ≤ 1 / t * (1 / t) :=
            mul_le_mul_of_nonneg_left hEK (by positivity)
        _ = 1 / t ^ 2 := by field_simp
    have h4 : 4 / ‖z i‖ ^ 2 ≤ 1 / t ^ 2 :=
      ((Real.log_le_iff_le_exp (by positivity)).1 hterm).trans hE
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h4
    by_contra hlt
    push_neg at hlt
    nlinarith
  set y := Real.log (1 / t) + K' with hy
  have hfar : ∀ x ∈ closedBall z t, ∀ i ∈ S, ‖z i‖ / 2 ≤ ‖x i‖ ∧ 0 < ‖x i‖ := by
    intro x hx i hi
    have h1 : ‖x i - z i‖ ≤ t :=
      (norm_le_pi_norm (x - z) i).trans (mem_closedBall_iff_norm.1 hx)
    have h2 := norm_sub_norm_le (z i) (x i)
    rw [norm_sub_rev] at h2
    have h3 := hcoord i hi
    constructor <;> linarith
  have hmem : ∀ x ∈ closedBall z t,
      x ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S := by
    intro x hx
    refine ⟨RegularChartScaling.closedBall_sub_of hzB (by linarith) hx, ?_⟩
    rintro ⟨i, hi, h0⟩
    have := (hfar x hx i hi).2
    rw [h0, norm_zero] at this
    exact lt_irrefl _ this
  have hrx : ∀ x ∈ closedBall z t, rLoc S m x ≤ y := by
    intro x hx
    have key : ∀ i ∈ S, (m i : ℝ) * Real.log (4 / ‖x i‖ ^ 2) ≤
        (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2) + (m i : ℝ) * Real.log 4 := by
      intro i hi
      obtain ⟨h1, h2⟩ := hfar x hx i hi
      have hzp : 0 < ‖z i‖ := norm_pos_iff.2 (hzi i hi)
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [← Real.log_mul (by positivity) (by norm_num)]
      refine Real.log_le_log (by positivity) ?_
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_self_le_mul_self (by positivity) h1]
    have hsum := Finset.sum_le_sum key
    rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
    unfold rLoc at hr ⊢
    simp only [hy, hK', RegularChartScaling.mTot]
    linarith
  set B := a * y ^ a * Real.exp (y / 2) with hB
  have hfd : ∀ x ∈ closedBall z t, ‖fderiv ℝ u x‖ ≤ B := by
    intro x hx
    have hxm := hmem x hx
    have hxn : ∀ i, ‖x i‖ ≤ 2 :=
      RegularChartScaling.norm_coord_le_of_ball (by norm_num : (3 / 2 : ℝ) ≤ 2) hxm.1
    have hr1 : 1 ≤ rLoc S m x := by
      have := RegularChartScaling.rLoc_ge S m hxn
      linarith [Real.add_one_le_exp (1 : ℝ)]
    have hry := hrx x hx
    have hy0 : 0 ≤ y := by linarith
    have hp : rLoc S m x ^ C₅ ≤ y ^ a :=
      (Real.rpow_le_rpow_of_exponent_le hr1 (le_abs_self C₅)).trans
        (Real.rpow_le_rpow (by linarith) hry (abs_nonneg _))
    refine (hg x hxm).trans ?_
    refine mul_le_mul (mul_le_mul (le_abs_self C₅) hp (Real.rpow_nonneg (by linarith) _)
      (abs_nonneg _)) (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
      (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hy0 _))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hfd z (mem_closedBall_self ht.le))
  have hBt : B * t ≤ t ^ ((1 : ℝ) / 3) / 2 := by
    have hlog : Real.log t = K' - y := by
      rw [hy, one_div, Real.log_inv]; ring
    have e : Real.exp (y / 2) * t = Real.exp (K' / 2) * t ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_def_of_pos ht, hlog]
      nth_rewrite 1 [← Real.exp_log ht]
      rw [hlog, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    calc B * t = a * y ^ a * (Real.exp (y / 2) * t) := by rw [hB]; ring
      _ = a * Real.exp (K' / 2) * y ^ a * t ^ ((1 : ℝ) / 2) := by rw [e]; ring
      _ ≤ t ^ ((1 : ℝ) / 3) / 2 := hsm t ht ht1
  unfold polyMaxOff
  refine csSup_le ⟨u z, z, ⟨mem_closedBall_self ht.le, hzD⟩, rfl⟩ ?_
  rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := u) (s := closedBall z t)
    (x := z) (y := x) (C := B)
    (fun w hw => (hd w (hmem w hw)).differentiableAt (hopen.mem_nhds (hmem w hw)))
    hfd (convex_closedBall z t) (mem_closedBall_self ht.le) hx
  have h1 : ‖x - z‖ ≤ t := mem_closedBall_iff_norm.1 hx
  have h2 : u x - u z ≤ ‖u x - u z‖ := Real.le_norm_self _
  have h3 : B * ‖x - z‖ ≤ B * t := mul_le_mul_of_nonneg_left h1 hB0
  linarith

end GlobalTheory.CompanionTheory.Ar.Giv
