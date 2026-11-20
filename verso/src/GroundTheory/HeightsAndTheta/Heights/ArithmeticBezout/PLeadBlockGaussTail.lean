import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsLeadBlockGaussTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Finset

open scoped ENNReal

noncomputable section

namespace LeadBlockGaussTail

/- English proof (translation)
The claim follows from `| 0, f, _ => by simp | n + 1, f, hf => by have e := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0 let g : E × (Fin n → E) → ℝ≥0∞ := fun a => f 0 a.1 * ∏ i : Fin n, f i.succ (a.2 i) have hg : Measurable fun a : Fin n → E => ∏ i : Fin n, f i.succ (a i) := Finset.mea …`.
-/
theorem lintegral_pi_prod {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] :
    ∀ (n : ℕ) (f : Fin n → E → ℝ≥0∞), (∀ i, Measurable (f i)) →
      ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi (fun _ => μ) = ∏ i, ∫⁻ y, f i y ∂μ
  | 0, f, _ => by simp
  | n + 1, f, hf => by
      have e := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
      let g : E × (Fin n → E) → ℝ≥0∞ := fun a => f 0 a.1 * ∏ i : Fin n, f i.succ (a.2 i)
      have hg : Measurable fun a : Fin n → E => ∏ i : Fin n, f i.succ (a i) :=
        Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)
      calc ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi (fun _ => μ)
          = ∫⁻ x, g (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0 x)
              ∂Measure.pi (fun _ => μ) := by
            refine lintegral_congr fun x => ?_
            simp [g, Fin.prod_univ_succ, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
            rfl
        _ = ∫⁻ a, g a ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) :=
            e.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) g
        _ = (∫⁻ y, f 0 y ∂μ) * ∫⁻ x, ∏ i : Fin n, f i.succ (x i) ∂(Measure.pi fun _ : Fin n => μ) :=
            lintegral_prod_mul (hf 0).aemeasurable hg.aemeasurable
        _ = ∏ i, ∫⁻ y, f i y ∂μ := by
            rw [lintegral_pi_prod μ n _ (fun i => hf i.succ), Fin.prod_univ_succ]

def halfGauss : ℝ≥0∞ := ∫⁻ z : ℂ, ENNReal.ofReal (Real.exp (-(‖z‖ ^ 2 / 2)))

/- English proof (translation)
Establish `h` using `(GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (1 / 2 : ℂ)) (by norm_num) 0 0).norm`. Establish `h2 : Integrable (fun z : ℂ => Real.exp (-(‖z‖ ^ 2 / 2)))`. Use `h.congr (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `only [Complex.norm_exp]`. Simplify using the standard rewrite rules.

Rewrite using `[← Complex.ofReal_pow, Complex.ofReal_re]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `h2.lintegral_lt_top`.
-/
theorem halfGauss_lt_top : halfGauss < ∞ := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (1 / 2 : ℂ))
    (by norm_num) 0 0).norm
  have h2 : Integrable (fun z : ℂ => Real.exp (-(‖z‖ ^ 2 / 2))) := by
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Complex.norm_exp]
    simp
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    ring
  exact h2.lintegral_lt_top

def entryConst : ℝ := 4 * (2 * halfGauss.toReal + Real.pi)

/- English proof (translation)
Unfold `entryConst`. Use `Real.pi_pos` as an intermediate fact. Establish `: 0 ≤ halfGauss.toReal` using `ENNReal.toReal_nonneg`. Check the signs of the components of the expression.
-/
theorem entryConst_pos : 0 < entryConst := by
  unfold entryConst
  have := Real.pi_pos
  have : 0 ≤ halfGauss.toReal := ENNReal.toReal_nonneg
  positivity

def ballInd (ρ : ℝ) (z : ℂ) : ℝ≥0∞ := {z : ℂ | |ρ| * ‖z‖ < 1}.indicator 1 z

/- English proof (translation)
The claim follows from `measurable_const.indicator (measurableSet_lt (by fun_prop) measurable_const)`.
-/
theorem measurable_ballInd (ρ : ℝ) : Measurable (ballInd ρ) :=
  measurable_const.indicator (measurableSet_lt (by fun_prop) measurable_const)

/- English proof (translation)
Unfold `ballInd Set.indicator`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ballInd_le_one (ρ : ℝ) (z : ℂ) : ballInd ρ z ≤ 1 := by
  unfold ballInd Set.indicator
  split_ifs <;> simp

/- English proof (translation)
Simplify using `[ballInd]`.
-/
theorem ballInd_zero (z : ℂ) : ballInd 0 z = 1 := by
  simp [ballInd]

/- English proof (translation)
Establish `h1` using `Real.add_one_le_exp (t / 2)`. Establish `h2 : Real.exp (-t) = Real.exp (-(t / 2)) * Real.exp (-(t / 2))`. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Establish `h3 : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1`.

Rewrite using `[← Real.exp_add]`. Simplify using the standard rewrite rules. Establish `h4` using `Real.exp_pos (-(t / 2))`. Establish `h5 : Real.exp (-(t / 2)) ≤ 1` using `Real.exp_le_one_iff.2 (by linarith)`. Use `interval_cases p`.

Rewrite using `[pow_zero, mul_one, h2]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[pow_one, h2]`. Use polynomial arithmetic with `[mul_pos h4 h4]`.
-/
theorem exp_mul_pow_le {t : ℝ} (ht : 0 ≤ t) {p : ℕ} (hp : p ≤ 1) :
    Real.exp (-t) * t ^ p ≤ 2 * Real.exp (-(t / 2)) := by
  have h1 := Real.add_one_le_exp (t / 2)
  have h2 : Real.exp (-t) = Real.exp (-(t / 2)) * Real.exp (-(t / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 := Real.exp_pos (-(t / 2))
  have h5 : Real.exp (-(t / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  interval_cases p
  · rw [pow_zero, mul_one, h2]; nlinarith
  · rw [pow_one, h2]; nlinarith [mul_pos h4 h4]

/- English proof (translation)
Establish `hG` using `halfGauss_lt_top`. Establish `hG0 : 0 ≤ halfGauss.toReal` using `ENNReal.toReal_nonneg`. Establish `hpi` using `Real.pi_pos`. Establish `hq : 0 < (1 + ρ ^ 2) ^ (p + 1)` using `by positivity`. Apply the tactic sequence `have h24 : (2 : ℝ) ^ (p + 1) ≤ 4 := by interval_cases p <;> norm_num`.

Break down `le_or_gt (ρ ^ 2) 1 with hρ | hρ` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun z => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_one, ← ENNReal.ofReal_mul (Real.exp_pos _).le]`.

Use `_ ≤ ENNReal.ofReal (2 * Real.exp (-(‖z‖ ^ 2 / 2))) := ENNReal.ofReal_le_ofReal (exp_mul_pow_le (by positivity) hp)`. Use `_ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; simp`. Use `_ = 2 * halfGauss := lintegral_const_mul' _ _ (by simp)`. Use `_ = ENNReal.ofReal (2 * halfGauss.toReal) := by`. Rewrite using `[ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hG.ne]; simp`.

Use `_ ≤ _ := by`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Rewrite using `[le_div_iff₀ hq]`. Establish `h4 : (1 + ρ ^ 2) ^ (p + 1) ≤ 4` using `(pow_le_pow_left₀ (by positivity) (by linarith) (p + 1)).trans h24`. Unfold `entryConst`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hρ0 : 0 < |ρ|` using `abs_pos.2 (by rintro rfl; norm_num at hρ)`. Establish `hset : {z : ℂ | |ρ| * ‖z‖ < 1} = Metric.ball (0 : ℂ) |ρ|⁻¹`. Use extensionality with `z`. Simplify using `only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]`.

Rewrite using `[← one_div, lt_div_iff₀ hρ0, mul_comm]`. Establish `hu : (|ρ|⁻¹) ^ 2 = (ρ ^ 2)⁻¹` using `by rw [inv_pow, sq_abs]`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun z => ?_` and prove the remaining obligations. Unfold `ballInd`.

Rewrite using `[hset]`. Distinguish the cases in `hz : z ∈ Metric.ball (0 : ℂ) |ρ|⁻¹`. Rewrite using `[Set.indicator_of_mem hz]`. Establish `hz' : ‖z‖ ^ 2 ≤ (ρ ^ 2)⁻¹`. Rewrite `hz` using `[Metric.mem_ball, dist_zero_right]`.

Rewrite using `[← hu]`. Conclude with `pow_le_pow_left₀ (norm_nonneg _) hz.le 2`. Establish `he : ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) ≤ 1` using `ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (by nlinarith [norm_nonneg z]))`. Combine the equalities or inequalities in the displayed calculation. Simplify using the standard rewrite rules.

Use `_ = _ := by simp`. Rewrite using `[Set.indicator_of_notMem hz]`. Simplify using the standard rewrite rules. Use `_ = ENNReal.ofReal (((ρ ^ 2)⁻¹) ^ p) * volume (Metric.ball (0 : ℂ) |ρ|⁻¹) := by`. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_one measurableSet_ball]`.

Use `_ = ENNReal.ofReal (((ρ ^ 2)⁻¹) ^ p * ((ρ ^ 2)⁻¹ * Real.pi)) := by`. Rewrite using `[Complex.volume_ball, ← ENNReal.ofReal_pow (inv_nonneg.2 hρ0.le), hu, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]`. Use `_ ≤ _ := by`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Rewrite using `[le_div_iff₀ hq]`.

Establish `hρ2 : 0 < ρ ^ 2` using `by linarith`. Establish `hu1 : (ρ ^ 2)⁻¹ * ρ ^ 2 = 1` using `inv_mul_cancel₀ hρ2.ne'`. Establish `hu0 : 0 < (ρ ^ 2)⁻¹` using `inv_pos.2 hρ2`. Establish `hule : (ρ ^ 2)⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ hρ.le`. Establish `key : (ρ ^ 2)⁻¹ * (1 + ρ ^ 2) = (ρ ^ 2)⁻¹ + 1` using `by rw [mul_add, hu1, mul_one]`.

Establish `h2 : ((ρ ^ 2)⁻¹) ^ p * ((ρ ^ 2)⁻¹ * Real.pi) * (1 + ρ ^ 2) ^ (p + 1) = Real.pi * ((ρ ^ 2)⁻¹ + 1) ^ (p + 1)`. Rewrite using `[← key, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ((ρ ^ 2)⁻¹ + 1) ^ (p + 1) ≤ 4` using `(pow_le_pow_left₀ (by positivity) (by linarith) (p + 1)).trans h24`. Rewrite using `[h2]`.

Unfold `entryConst`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem entry_bound (ρ : ℝ) (p : ℕ) (hp : p ≤ 1) :
    ∫⁻ z : ℂ, ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) * ENNReal.ofReal ((‖z‖ ^ 2) ^ p) * ballInd ρ z ≤
      ENNReal.ofReal (entryConst / (1 + ρ ^ 2) ^ (p + 1)) := by
  have hG := halfGauss_lt_top
  have hG0 : 0 ≤ halfGauss.toReal := ENNReal.toReal_nonneg
  have hpi := Real.pi_pos
  have hq : 0 < (1 + ρ ^ 2) ^ (p + 1) := by positivity
  have h24 : (2 : ℝ) ^ (p + 1) ≤ 4 := by interval_cases p <;> norm_num
  rcases le_or_gt (ρ ^ 2) 1 with hρ | hρ
  · calc _ ≤ ∫⁻ z : ℂ, 2 * ENNReal.ofReal (Real.exp (-(‖z‖ ^ 2 / 2))) := by
          refine lintegral_mono fun z => ?_
          calc _ ≤ ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) * ENNReal.ofReal ((‖z‖ ^ 2) ^ p) * 1 := by
                gcongr; exact ballInd_le_one ρ z
            _ = ENNReal.ofReal (Real.exp (-‖z‖ ^ 2) * (‖z‖ ^ 2) ^ p) := by
                rw [mul_one, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
            _ ≤ ENNReal.ofReal (2 * Real.exp (-(‖z‖ ^ 2 / 2))) :=
                ENNReal.ofReal_le_ofReal (exp_mul_pow_le (by positivity) hp)
            _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; simp
      _ = 2 * halfGauss := lintegral_const_mul' _ _ (by simp)
      _ = ENNReal.ofReal (2 * halfGauss.toReal) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hG.ne]; simp
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [le_div_iff₀ hq]
          have h4 : (1 + ρ ^ 2) ^ (p + 1) ≤ 4 :=
            (pow_le_pow_left₀ (by positivity) (by linarith) (p + 1)).trans h24
          unfold entryConst
          nlinarith
  · have hρ0 : 0 < |ρ| := abs_pos.2 (by rintro rfl; norm_num at hρ)
    have hset : {z : ℂ | |ρ| * ‖z‖ < 1} = Metric.ball (0 : ℂ) |ρ|⁻¹ := by
      ext z
      simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
      rw [← one_div, lt_div_iff₀ hρ0, mul_comm]
    have hu : (|ρ|⁻¹) ^ 2 = (ρ ^ 2)⁻¹ := by rw [inv_pow, sq_abs]
    calc _ ≤ ∫⁻ z : ℂ, ENNReal.ofReal (((ρ ^ 2)⁻¹) ^ p) *
          (Metric.ball (0 : ℂ) |ρ|⁻¹).indicator 1 z := by
          refine lintegral_mono fun z => ?_
          unfold ballInd
          rw [hset]
          by_cases hz : z ∈ Metric.ball (0 : ℂ) |ρ|⁻¹
          · rw [Set.indicator_of_mem hz]
            have hz' : ‖z‖ ^ 2 ≤ (ρ ^ 2)⁻¹ := by
              rw [Metric.mem_ball, dist_zero_right] at hz
              rw [← hu]; exact pow_le_pow_left₀ (norm_nonneg _) hz.le 2
            have he : ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) ≤ 1 :=
              ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (by nlinarith [norm_nonneg z]))
            calc _ ≤ 1 * ENNReal.ofReal (((ρ ^ 2)⁻¹) ^ p) * 1 := by
                  gcongr
                  simp
              _ = _ := by simp
          · rw [Set.indicator_of_notMem hz]; simp
      _ = ENNReal.ofReal (((ρ ^ 2)⁻¹) ^ p) * volume (Metric.ball (0 : ℂ) |ρ|⁻¹) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_one measurableSet_ball]
      _ = ENNReal.ofReal (((ρ ^ 2)⁻¹) ^ p * ((ρ ^ 2)⁻¹ * Real.pi)) := by
          rw [Complex.volume_ball, ← ENNReal.ofReal_pow (inv_nonneg.2 hρ0.le), hu,
            ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [le_div_iff₀ hq]
          have hρ2 : 0 < ρ ^ 2 := by linarith
          have hu1 : (ρ ^ 2)⁻¹ * ρ ^ 2 = 1 := inv_mul_cancel₀ hρ2.ne'
          have hu0 : 0 < (ρ ^ 2)⁻¹ := inv_pos.2 hρ2
          have hule : (ρ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hρ.le
          have key : (ρ ^ 2)⁻¹ * (1 + ρ ^ 2) = (ρ ^ 2)⁻¹ + 1 := by rw [mul_add, hu1, mul_one]
          have h2 : ((ρ ^ 2)⁻¹) ^ p * ((ρ ^ 2)⁻¹ * Real.pi) * (1 + ρ ^ 2) ^ (p + 1) =
              Real.pi * ((ρ ^ 2)⁻¹ + 1) ^ (p + 1) := by
            rw [← key, mul_pow]; ring
          have h3 : ((ρ ^ 2)⁻¹ + 1) ^ (p + 1) ≤ 4 :=
            (pow_le_pow_left₀ (by positivity) (by linarith) (p + 1)).trans h24
          rw [h2]
          unfold entryConst
          nlinarith

/- English proof (translation)
Establish `h1 : ‖(coordPlaneBlock π).det‖ ≤ ∑ σ : Equiv.Perm (Fin m), ∏ i, ‖π i (Fin.castAdd k (σ i))‖`. Rewrite using `[← Matrix.det_transpose, Matrix.det_apply]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>`. Simplify using `[h, norm_prod, coordPlaneBlock, Matrix.transpose_apply]`.

Combine the equalities or inequalities in the displayed calculation. Use `sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Equiv.Perm (Fin m)))) (f := fun σ => ∏ i, ‖π i (Fin.castAdd k (σ i))‖)` as an intermediate fact. Simplify `this` using `[Finset.card_univ, Finset.prod_pow]`.
-/
theorem norm_det_sq_le {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ) :
    ‖(coordPlaneBlock π).det‖ ^ 2 ≤ (Fintype.card (Equiv.Perm (Fin m)) : ℝ) *
      ∑ σ : Equiv.Perm (Fin m), ∏ i, ‖π i (Fin.castAdd k (σ i))‖ ^ 2 := by
  have h1 : ‖(coordPlaneBlock π).det‖ ≤
      ∑ σ : Equiv.Perm (Fin m), ∏ i, ‖π i (Fin.castAdd k (σ i))‖ := by
    rw [← Matrix.det_transpose, Matrix.det_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
      simp [h, norm_prod, coordPlaneBlock, Matrix.transpose_apply]
  calc ‖(coordPlaneBlock π).det‖ ^ 2
      ≤ (∑ σ : Equiv.Perm (Fin m), ∏ i, ‖π i (Fin.castAdd k (σ i))‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by
        have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Equiv.Perm (Fin m))))
          (f := fun σ => ∏ i, ‖π i (Fin.castAdd k (σ i))‖)
        simpa [Finset.card_univ, Finset.prod_pow] using this

/- English proof (translation)
Simplify using `only [linProj, firstCoordVec]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_single c0]`. Simplify using `[hc0, mul_comm]`. Introduce `j _ hj`.

Establish `: (j : ℕ) ≠ 0` using `fun h => hj (Fin.ext (h.trans hc0.symm))`. Simplify using `[this]`. Simplify using the standard rewrite rules.
-/
theorem linProj_smul_firstCoordVec {m n : ℕ} (π : Fin m → Fin n → ℂ) (r : ℝ) (c0 : Fin n)
    (hc0 : (c0 : ℕ) = 0) (i : Fin m) :
    linProj π ((r : ℂ) • firstCoordVec n) i = (r : ℂ) * π i c0 := by
  simp only [linProj, firstCoordVec]
  simp
  rw [Finset.sum_eq_single c0]
  · simp [hc0, mul_comm]
  · intro j _ hj
    have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext (h.trans hc0.symm))
    simp [this]
  · simp

/- English proof (translation)
Distinguish the cases in `hv : linProj π ((r : ℂ) • firstCoordVec n) ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1`. Rewrite using `[Set.indicator_of_mem hv]`. Establish `: ∀ i, ballInd r (π i c0) = 1`. Introduce `i`. Establish `hi` using `PiLp.norm_apply_le (linProj π ((r : ℂ) • firstCoordVec n)) i`.

Rewrite `hi` using `[linProj_smul_firstCoordVec π r c0 hc0 i, norm_mul, Complex.norm_real, Real.norm_eq_abs]`. Rewrite `hv` using `[Metric.mem_ball, dist_zero_right]`. Simplify using `[ballInd, Set.indicator, show |r| * ‖π i c0‖ < 1 from hi.trans_lt hv]`. Simplify using `[this]`. Rewrite using `[Set.indicator_of_notMem hv]`.

Conclude with `bot_le`.
-/
theorem ball_indicator_le {m n : ℕ} (π : Fin m → Fin n → ℂ) (r : ℝ) (c0 : Fin n)
    (hc0 : (c0 : ℕ) = 0) :
    (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π ((r : ℂ) • firstCoordVec n)) ≤
      ∏ i, ballInd r (π i c0) := by
  by_cases hv : linProj π ((r : ℂ) • firstCoordVec n) ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1
  · rw [Set.indicator_of_mem hv]
    have : ∀ i, ballInd r (π i c0) = 1 := by
      intro i
      have hi := PiLp.norm_apply_le (linProj π ((r : ℂ) • firstCoordVec n)) i
      rw [linProj_smul_firstCoordVec π r c0 hc0 i, norm_mul, Complex.norm_real,
        Real.norm_eq_abs] at hi
      rw [Metric.mem_ball, dist_zero_right] at hv
      simp [ballInd, Set.indicator, show |r| * ‖π i c0‖ < 1 from hi.trans_lt hv]
    simp [this]
  · rw [Set.indicator_of_notMem hv]; exact bot_le

/- English proof (translation)
Unfold `matGauss`. Rewrite using `[← Finset.sum_neg_distrib, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]`.
-/
theorem matGauss_eq_prod {m n : ℕ} (π : Fin m → Fin n → ℂ) :
    matGauss π = ∏ i, ∏ j, ENNReal.ofReal (Real.exp (-‖π i j‖ ^ 2)) := by
  unfold matGauss
  rw [← Finset.sum_neg_distrib, Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib, Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]

def entryFn (r : ℝ) {n : ℕ} (c0 s j : Fin n) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) * ENNReal.ofReal ((‖z‖ ^ 2) ^ (if j = s then 1 else 0)) *
    ballInd (if j = c0 then r else 0) z

/- English proof (translation)
Establish `hc0 : ((Fin.castAdd k (⟨0, hm⟩ : Fin m) : Fin (m + k)) : ℕ) = 0` using `rfl`. Establish `hrow : ∀ σ : Equiv.Perm (Fin m), ∏ i, ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (π i j) = matGauss π * ENNReal.ofReal (∏ i, ‖π i (Fin.castAdd k (σ i))‖ ^ 2) * ∏ i, ballInd r (π i (Fin.castAdd k ⟨0, hm⟩))`. Introduce `σ`. Rewrite using `[matGauss_eq_prod, ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]`. Simplify using `only [entryFn, Finset.prod_mul_distrib]`.

Use `congr 1`. Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single (Fin.castAdd k (σ i)) (fun j _ hj => by simp [hj]) (by simp)]`. Simplify using the standard rewrite rules.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_eq_single (Fin.castAdd k ⟨0, hm⟩) (fun j _ hj => by simp only [if_neg hj, ballInd_zero]) (by simp)]`. Simplify using the standard rewrite rules. Repeatedly rewrite using `[hrow]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `ball_indicator_le π r _ hc0`. Conclude with `norm_det_sq_le π`. Use `_ = _ := by`. Rewrite using `[ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun σ _ => by positivity)]`. Simplify using `only [Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integrand_le {m k : ℕ} (hm : 0 < m) (r : ℝ) (π : Fin m → Fin (m + k) → ℂ) :
    matGauss π * (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
        (linProj π ((r : ℂ) • firstCoordVec (m + k))) *
        ENNReal.ofReal (‖(coordPlaneBlock π).det‖ ^ 2) ≤
      ENNReal.ofReal (Fintype.card (Equiv.Perm (Fin m))) * ∑ σ : Equiv.Perm (Fin m),
        ∏ i, ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (π i j) := by
  have hc0 : ((Fin.castAdd k (⟨0, hm⟩ : Fin m) : Fin (m + k)) : ℕ) = 0 := rfl
  have hrow : ∀ σ : Equiv.Perm (Fin m),
      ∏ i, ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (π i j) =
      matGauss π * ENNReal.ofReal (∏ i, ‖π i (Fin.castAdd k (σ i))‖ ^ 2) *
        ∏ i, ballInd r (π i (Fin.castAdd k ⟨0, hm⟩)) := by
    intro σ
    rw [matGauss_eq_prod, ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    simp only [entryFn, Finset.prod_mul_distrib]
    congr 1
    · congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Finset.prod_eq_single (Fin.castAdd k (σ i)) (fun j _ hj => by simp [hj]) (by simp)]
      simp
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [Finset.prod_eq_single (Fin.castAdd k ⟨0, hm⟩) (fun j _ hj => by simp only [if_neg hj, ballInd_zero])
        (by simp)]
      simp
  simp_rw [hrow]
  calc _ ≤ matGauss π * (∏ i, ballInd r (π i (Fin.castAdd k ⟨0, hm⟩))) *
        ENNReal.ofReal ((Fintype.card (Equiv.Perm (Fin m)) : ℝ) *
          ∑ σ : Equiv.Perm (Fin m), ∏ i, ‖π i (Fin.castAdd k (σ i))‖ ^ 2) := by
        gcongr
        · exact ball_indicator_le π r _ hc0
        · exact norm_det_sq_le π
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun σ _ => by positivity)]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        ring

/- English proof (translation)
Establish `hrow : ∀ i : Fin m, ∏ j : Fin (m + k), (1 + (if j = Fin.castAdd k ⟨0, hm⟩ then r else 0) ^ 2) ^ ((if j = Fin.castAdd k (σ i) then 1 else 0) + 1) = (1 + r ^ 2) ^ ((if Fin.castAdd k (⟨0, hm⟩ : Fin m) = Fin.castAdd k (σ i) then 1 else 0) + 1)`. Introduce `i`. Rewrite using `[Finset.prod_eq_single (Fin.castAdd k ⟨0, hm⟩) (fun j _ hj => by simp only [if_neg hj]; simp) (by simp)]`. Simplify using the standard rewrite rules. Establish `hsum : ∑ i : Fin m, ((if Fin.castAdd k (⟨0, hm⟩ : Fin m) = Fin.castAdd k (σ i) then 1 else 0) + 1) = m + 1`.

Establish `h : ∀ i : Fin m, (Fin.castAdd k (⟨0, hm⟩ : Fin m) = Fin.castAdd k (σ i)) ↔ (σ.symm ⟨0, hm⟩ = i)`. Introduce `i`. Rewrite using `[(Fin.castAdd_injective _ _).eq_iff, Equiv.symm_apply_eq]`. Repeatedly rewrite using `[h]`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_ite_eq]`.

Simplify using `[add_comm]`. Repeatedly rewrite using `[Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hrow, Finset.prod_pow_eq_pow_sum, hsum, ← pow_mul]`. Put the polynomial expressions in normal form.
-/
theorem prod_entry_eq {m k : ℕ} (hm : 0 < m) (K r : ℝ) (σ : Equiv.Perm (Fin m)) :
    ∏ i : Fin m, ∏ j : Fin (m + k), K / (1 + (if j = Fin.castAdd k ⟨0, hm⟩ then r else 0) ^ 2) ^
        ((if j = Fin.castAdd k (σ i) then 1 else 0) + 1) =
      K ^ (m * (m + k)) / (1 + r ^ 2) ^ (m + 1) := by
  have hrow : ∀ i : Fin m, ∏ j : Fin (m + k),
      (1 + (if j = Fin.castAdd k ⟨0, hm⟩ then r else 0) ^ 2) ^
        ((if j = Fin.castAdd k (σ i) then 1 else 0) + 1) =
      (1 + r ^ 2) ^ ((if Fin.castAdd k (⟨0, hm⟩ : Fin m) = Fin.castAdd k (σ i) then 1 else 0) + 1) := by
    intro i
    rw [Finset.prod_eq_single (Fin.castAdd k ⟨0, hm⟩) (fun j _ hj => by simp only [if_neg hj]; simp)
      (by simp)]
    simp
  have hsum : ∑ i : Fin m,
      ((if Fin.castAdd k (⟨0, hm⟩ : Fin m) = Fin.castAdd k (σ i) then 1 else 0) + 1) = m + 1 := by
    have h : ∀ i : Fin m, (Fin.castAdd k (⟨0, hm⟩ : Fin m) = Fin.castAdd k (σ i)) ↔
        (σ.symm ⟨0, hm⟩ = i) := by
      intro i
      rw [(Fin.castAdd_injective _ _).eq_iff, Equiv.symm_apply_eq]
    simp_rw [h]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp [add_comm]
  simp_rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hrow,
    Finset.prod_pow_eq_pow_sum, hsum, ← pow_mul]
  ring_nf

/- English proof (translation)
Introduce `m k hm`. Use `set N : ℝ := (Fintype.card (Equiv.Perm (Fin m)) : ℝ) with hN`. Establish `hN0 : 0 ≤ N` using `Nat.cast_nonneg _`. Establish `hK` using `entryConst_pos`. Use `⟨N * (N * entryConst ^ (m * (m + k))), fun r => ?_⟩` and prove the remaining obligations.

Establish `hφ : ∀ s j : Fin (m + k), Measurable (entryFn r (Fin.castAdd k ⟨0, hm⟩) s j)` using `fun s j => ((ENNReal.measurable_ofReal.comp (by fun_prop)).mul (ENNReal.measurable_ofReal.comp (by fun_prop))).mul (measurable_ballInd _)`. Establish `hrowm : ∀ σ : Equiv.Perm (Fin m), ∀ i : Fin m, Measurable fun x : Fin (m + k) → ℂ => ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (x j)` using `fun σ i => Finset.measurable_prod _ fun j _ => (hφ _ j).comp (measurable_pi_apply j)`. Establish `hq : 0 < (1 + r ^ 2) ^ (m + 1)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `hmeas : ∀ σ : Equiv.Perm (Fin m), Measurable fun π : Fin m → Fin (m + k) → ℂ => ∏ i, ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (π i j)` using `fun σ => Finset.measurable_prod _ fun i _ => (hrowm σ i).comp (measurable_pi_apply i)`.

Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum _ (fun σ _ => hmeas σ)]`. Use `congr 1`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[volume_pi, lintegral_pi_prod _ m _ (hrowm σ)]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[volume_pi, lintegral_pi_prod _ (m + k) _ (fun j => hφ _ j)]`. Use `_ ≤ ENNReal.ofReal N * ∑ σ : Equiv.Perm (Fin m), ∏ i : Fin m, ∏ j : Fin (m + k), ENNReal.ofReal (entryConst / (1 + (if j = Fin.castAdd k ⟨0, hm⟩ then r else 0) ^ 2) ^ ((if j = Fin.castAdd k (σ i) then 1 else 0) + 1)) := by gcongr with σ _ i _ j _`. Apply the tactic sequence `exact entry_bound _ _ (by split_ifs <;> omega)`. Use `_ = ENNReal.ofReal N * ∑ σ : Equiv.Perm (Fin m), ENNReal.ofReal (entryConst ^ (m * (m + k)) / (1 + r ^ 2) ^ (m + 1)) := by`. Use `congr 1`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_congr rfl fun i _ => (ENNReal.ofReal_prod_of_nonneg fun j _ => div_nonneg hK.le (by positivity)).symm, ← ENNReal.ofReal_prod_of_nonneg fun i _ => Finset.prod_nonneg fun j _ => div_nonneg hK.le (by positivity), prod_entry_eq hm]`. Use `_ = ENNReal.ofReal (N * (N * entryConst ^ (m * (m + k))) / (1 + r ^ 2) ^ (m + 1)) := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul hN0]`. Use `congr 1`.

Rewrite using `[hN]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem proof : LeadBlockGaussTail.Statement := by
  intro m k hm
  set N : ℝ := (Fintype.card (Equiv.Perm (Fin m)) : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hK := entryConst_pos
  refine ⟨N * (N * entryConst ^ (m * (m + k))), fun r => ?_⟩
  have hφ : ∀ s j : Fin (m + k), Measurable (entryFn r (Fin.castAdd k ⟨0, hm⟩) s j) := fun s j =>
    ((ENNReal.measurable_ofReal.comp (by fun_prop)).mul
      (ENNReal.measurable_ofReal.comp (by fun_prop))).mul (measurable_ballInd _)
  have hrowm : ∀ σ : Equiv.Perm (Fin m), ∀ i : Fin m, Measurable fun x : Fin (m + k) → ℂ =>
      ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (x j) :=
    fun σ i => Finset.measurable_prod _ fun j _ => (hφ _ j).comp (measurable_pi_apply j)
  have hq : 0 < (1 + r ^ 2) ^ (m + 1) := by positivity
  calc _ ≤ ∫⁻ π : Fin m → Fin (m + k) → ℂ, ENNReal.ofReal N * ∑ σ : Equiv.Perm (Fin m),
          ∏ i, ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (π i j) :=
        lintegral_mono (integrand_le hm r)
    _ = ENNReal.ofReal N * ∑ σ : Equiv.Perm (Fin m),
          ∏ i, ∏ j, ∫⁻ z, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j z := by
        have hmeas : ∀ σ : Equiv.Perm (Fin m), Measurable fun π : Fin m → Fin (m + k) → ℂ =>
            ∏ i, ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (π i j) :=
          fun σ => Finset.measurable_prod _ fun i _ => (hrowm σ i).comp (measurable_pi_apply i)
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum _ (fun σ _ => hmeas σ)]
        congr 1
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [volume_pi, lintegral_pi_prod _ m _ (hrowm σ)]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [volume_pi, lintegral_pi_prod _ (m + k) _ (fun j => hφ _ j)]
    _ ≤ ENNReal.ofReal N * ∑ σ : Equiv.Perm (Fin m), ∏ i : Fin m, ∏ j : Fin (m + k),
          ENNReal.ofReal (entryConst / (1 + (if j = Fin.castAdd k ⟨0, hm⟩ then r else 0) ^ 2) ^
            ((if j = Fin.castAdd k (σ i) then 1 else 0) + 1)) := by
        gcongr with σ _ i _ j _
        exact entry_bound _ _ (by split_ifs <;> omega)
    _ = ENNReal.ofReal N * ∑ σ : Equiv.Perm (Fin m),
          ENNReal.ofReal (entryConst ^ (m * (m + k)) / (1 + r ^ 2) ^ (m + 1)) := by
        congr 1
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.prod_congr rfl fun i _ =>
            (ENNReal.ofReal_prod_of_nonneg fun j _ => div_nonneg hK.le (by positivity)).symm,
          ← ENNReal.ofReal_prod_of_nonneg fun i _ =>
            Finset.prod_nonneg fun j _ => div_nonneg hK.le (by positivity),
          prod_entry_eq hm]
    _ = ENNReal.ofReal (N * (N * entryConst ^ (m * (m + k))) / (1 + r ^ 2) ^ (m + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_mul hN0]
        congr 1
        rw [hN]
        ring

end LeadBlockGaussTail

end

end GroundTheory.Heights₂.Heights
