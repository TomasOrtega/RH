import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableBoundedMulWeightFive

open MeasureTheory Matrix Filter Topology
open Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.ParsC

noncomputable section

namespace GlobalTheory.CompanionTheory.ParsC.GaussB

def Kf (w : ℂ) : ℝ := (1 + ‖w‖ ^ 2) * Real.exp (-Real.pi * ‖w‖ ^ 2)

/- English proof (translation)
Establish `hE : 1 + t ^ 2 / 3 ≤ Real.exp (t ^ 2 / 3)`. Use `Real.add_one_le_exp (t ^ 2 / 3)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : Real.exp (t ^ 2 / 3) ^ 3 = Real.exp (t ^ 2)`. Rewrite using `[← Real.exp_nat_mul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : 1 + t ^ 2 ≤ 3 * Real.exp (t ^ 2 / 3)` using `by nlinarith [sq_nonneg t]`. Establish `h4 : (1 + t ^ 2) ^ 3 ≤ 27 * Real.exp (t ^ 2)`.

Establish `: (1 + t ^ 2) ^ 3 ≤ (3 * Real.exp (t ^ 2 / 3)) ^ 3` using `pow_le_pow_left₀ (by positivity) h1 3`. Combine the equalities or inequalities in the displayed calculation. Establish `h5 : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2)` using `by nlinarith [sq_nonneg (t - 1)]`. Establish `h6 : (1 + t) ^ 6 ≤ 8 * (1 + t ^ 2) ^ 3`. Establish `: ((1 + t) ^ 2) ^ 3 ≤ (2 * (1 + t ^ 2)) ^ 3` using `pow_le_pow_left₀ (by positivity) h5 3`.

Combine the equalities or inequalities in the displayed calculation. Establish `h7 : (1 + t) ^ 3 * (1 + t ^ 2) ≤ (1 + t) ^ 6`. Establish `a : 1 + t ^ 2 ≤ (1 + t) ^ 2` using `by nlinarith`. Establish `b : (1 : ℝ) ≤ 1 + t` using `by linarith`. Combine the equalities or inequalities in the displayed calculation.

Establish `h8 : Real.exp (t ^ 2) ≤ Real.exp (Real.pi * t ^ 2)`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Use polynomial arithmetic with `[Real.pi_gt_three, sq_nonneg t]`. Establish `h9 : (1 + t) ^ 3 * (1 + t ^ 2) ≤ 216 * Real.exp (Real.pi * t ^ 2)` using `by linarith`. Establish `h10 : Real.exp (Real.pi * t ^ 2) * Real.exp (-Real.pi * t ^ 2) = 1`.

Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.
-/
lemma poly_mul_gaussian_le_const (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ 3 * ((1 + t ^ 2) * Real.exp (-Real.pi * t ^ 2)) ≤ 216 := by
  have hE : 1 + t ^ 2 / 3 ≤ Real.exp (t ^ 2 / 3) := by
    have := Real.add_one_le_exp (t ^ 2 / 3); linarith
  have h3 : Real.exp (t ^ 2 / 3) ^ 3 = Real.exp (t ^ 2) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h1 : 1 + t ^ 2 ≤ 3 * Real.exp (t ^ 2 / 3) := by nlinarith [sq_nonneg t]
  have h4 : (1 + t ^ 2) ^ 3 ≤ 27 * Real.exp (t ^ 2) := by
    have : (1 + t ^ 2) ^ 3 ≤ (3 * Real.exp (t ^ 2 / 3)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h1 3
    calc (1 + t ^ 2) ^ 3 ≤ (3 * Real.exp (t ^ 2 / 3)) ^ 3 := this
      _ = 27 * Real.exp (t ^ 2 / 3) ^ 3 := by ring
      _ = 27 * Real.exp (t ^ 2) := by rw [h3]
  have h5 : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (t - 1)]
  have h6 : (1 + t) ^ 6 ≤ 8 * (1 + t ^ 2) ^ 3 := by
    have : ((1 + t) ^ 2) ^ 3 ≤ (2 * (1 + t ^ 2)) ^ 3 := pow_le_pow_left₀ (by positivity) h5 3
    calc (1 + t) ^ 6 = ((1 + t) ^ 2) ^ 3 := by ring
      _ ≤ (2 * (1 + t ^ 2)) ^ 3 := this
      _ = 8 * (1 + t ^ 2) ^ 3 := by ring
  have h7 : (1 + t) ^ 3 * (1 + t ^ 2) ≤ (1 + t) ^ 6 := by
    have a : 1 + t ^ 2 ≤ (1 + t) ^ 2 := by nlinarith
    have b : (1 : ℝ) ≤ 1 + t := by linarith
    calc (1 + t) ^ 3 * (1 + t ^ 2) ≤ (1 + t) ^ 3 * (1 + t) ^ 2 := by gcongr
      _ = (1 + t) ^ 5 * 1 := by ring
      _ ≤ (1 + t) ^ 5 * (1 + t) := by gcongr
      _ = (1 + t) ^ 6 := by ring
  have h8 : Real.exp (t ^ 2) ≤ Real.exp (Real.pi * t ^ 2) := by
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_gt_three, sq_nonneg t]
  have h9 : (1 + t) ^ 3 * (1 + t ^ 2) ≤ 216 * Real.exp (Real.pi * t ^ 2) := by linarith
  have h10 : Real.exp (Real.pi * t ^ 2) * Real.exp (-Real.pi * t ^ 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  calc (1 + t) ^ 3 * ((1 + t ^ 2) * Real.exp (-Real.pi * t ^ 2))
      = ((1 + t) ^ 3 * (1 + t ^ 2)) * Real.exp (-Real.pi * t ^ 2) := by ring
    _ ≤ (216 * Real.exp (Real.pi * t ^ 2)) * Real.exp (-Real.pi * t ^ 2) := by gcongr
    _ = 216 := by rw [mul_assoc, h10, mul_one]

/- English proof (translation)
Unfold `Kf`. Check the signs of the components of the expression.
-/
lemma Kf_nonneg (w : ℂ) : 0 ≤ Kf w := by unfold Kf; positivity

/- English proof (translation)
Establish `h` using `poly_mul_gaussian_le_const ‖w‖ (norm_nonneg w)`. Establish `h1 : (1 : ℝ) ≤ (1 + ‖w‖) ^ 3` using `one_le_pow₀ (by linarith [norm_nonneg w])`. Establish `h0` using `Kf_nonneg w`. Unfold `Kf at *`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma Kf_le (w : ℂ) : Kf w ≤ 216 := by
  have h := poly_mul_gaussian_le_const ‖w‖ (norm_nonneg w)
  have h1 : (1 : ℝ) ≤ (1 + ‖w‖) ^ 3 := one_le_pow₀ (by linarith [norm_nonneg w])
  have h0 := Kf_nonneg w
  unfold Kf at *
  nlinarith

/- English proof (translation)
Unfold `Kf`. Use `fun_prop`.
-/
lemma Kf_cont : Continuous Kf := by unfold Kf; fun_prop

/- English proof (translation)
Establish `hr : ((Module.finrank ℝ ℂ : ℕ) : ℝ) < (3 : ℝ)`. Rewrite using `[Complex.finrank_real_complex]`. Evaluate the numerical expressions. Establish `h` using `(integrable_one_add_norm (E := ℂ) (μ := volume) hr).const_mul 216`. Use `h.mono' Kf_cont.aestronglyMeasurable (Eventually.of_forall fun w => ?_)` and prove the remaining obligations.

Rewrite using `[Real.norm_of_nonneg (Kf_nonneg w)]`. Establish `hp : 0 < 1 + ‖w‖` using `by positivity`. Rewrite using `[Real.rpow_neg hp.le]`. Establish `e : (1 + ‖w‖) ^ (3 : ℝ) = (1 + ‖w‖) ^ 3` using `by norm_cast`. Rewrite using `[e, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]`.

Use `poly_mul_gaussian_le_const ‖w‖ (norm_nonneg w)` as an intermediate fact. Unfold `Kf`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Kf_int : Integrable Kf := by
  have hr : ((Module.finrank ℝ ℂ : ℕ) : ℝ) < (3 : ℝ) := by
    rw [Complex.finrank_real_complex]; norm_num
  have h := (integrable_one_add_norm (E := ℂ) (μ := volume) hr).const_mul 216
  refine h.mono' Kf_cont.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
  rw [Real.norm_of_nonneg (Kf_nonneg w)]
  have hp : 0 < 1 + ‖w‖ := by positivity
  rw [Real.rpow_neg hp.le]
  have e : (1 + ‖w‖) ^ (3 : ℝ) = (1 + ‖w‖) ^ 3 := by norm_cast
  rw [e, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have := poly_mul_gaussian_le_const ‖w‖ (norm_nonneg w)
  unfold Kf
  linarith

/- English proof (translation)
The claim follows from `(Kf_int.comp_smul hε.ne').comp_sub_right v`.
-/
lemma Ks_int (ε : ℝ) (hε : 0 < ε) (v : ℂ) : Integrable (fun w : ℂ => Kf (ε • (w - v))) :=
  (Kf_int.comp_smul hε.ne').comp_sub_right v

/- English proof (translation)
Establish `h1` using `integral_sub_right_eq_self (μ := (volume : Measure ℂ)) (fun u : ℂ => Kf (ε • u)) v`. Rewrite using `[h1, Measure.integral_comp_smul volume Kf ε, Complex.finrank_real_complex, smul_eq_mul, abs_of_pos (by positivity)]`.
-/
lemma Ks_integral (ε : ℝ) (hε : 0 < ε) (v : ℂ) :
    ∫ w : ℂ, Kf (ε • (w - v)) = (ε ^ 2)⁻¹ * ∫ w, Kf w := by
  have h1 := integral_sub_right_eq_self (μ := (volume : Measure ℂ)) (fun u : ℂ => Kf (ε • u)) v
  rw [h1, Measure.integral_comp_smul volume Kf ε, Complex.finrank_real_complex, smul_eq_mul,
    abs_of_pos (by positivity)]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma gw_eq (ε : ℝ) (v w : ℂ) : gw ε v w = Real.exp (-Real.pi * ε ^ 2 * ‖w - v‖ ^ 2) := rfl

/- English proof (translation)
Establish `hn : ‖ε • (w - v)‖ = ε * ‖w - v‖`. Rewrite using `[norm_smul, Real.norm_of_nonneg hε.le]`. Unfold `Kf`. Rewrite using `[hn, gw_eq]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma Ks_eq (ε : ℝ) (hε : 0 < ε) (v w : ℂ) :
    Kf (ε • (w - v)) = (1 + (ε * ‖w - v‖) ^ 2) * gw ε v w := by
  have hn : ‖ε • (w - v)‖ = ε * ‖w - v‖ := by
    rw [norm_smul, Real.norm_of_nonneg hε.le]
  unfold Kf
  rw [hn, gw_eq]
  congr 2
  ring

/- English proof (translation)
The claim follows from `Real.exp_pos _`.
-/
lemma gw_pos (ε : ℝ) (v w : ℂ) : 0 < gw ε v w := Real.exp_pos _

/- English proof (translation)
Rewrite using `[gw_eq, Real.exp_le_one_iff]`. Establish `: 0 ≤ Real.pi * ε ^ 2 * ‖w - v‖ ^ 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma gw_le (ε : ℝ) (v w : ℂ) : gw ε v w ≤ 1 := by
  rw [gw_eq, Real.exp_le_one_iff]
  have : 0 ≤ Real.pi * ε ^ 2 * ‖w - v‖ ^ 2 := by positivity
  linarith

/- English proof (translation)
Establish `: gw ε v = fun w => Real.exp (-Real.pi * ε ^ 2 * ‖w - v‖ ^ 2)` using `rfl`. Rewrite using `[this]`. Use `fun_prop`.
-/
lemma gw_cont (ε : ℝ) (v : ℂ) : Continuous (gw ε v) := by
  have : gw ε v = fun w => Real.exp (-Real.pi * ε ^ 2 * ‖w - v‖ ^ 2) := rfl
  rw [this]; fun_prop

/- English proof (translation)
Establish `h` using `gw_cont ε v`. Establish `: G1 ε v c = fun w => -2 * Real.pi * ε ^ 2 * (((starRingEnd ℂ) c * (w - v)).re) * gw ε v w` using `rfl`. Rewrite using `[this]`. Conclude with `((continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul (continuous_id.sub continuous_const))))).mul h`.
-/
lemma continuous_firstGaussDeriv (ε : ℝ) (v c : ℂ) : Continuous (G1 ε v c) := by
  have h := gw_cont ε v
  have : G1 ε v c = fun w => -2 * Real.pi * ε ^ 2 * (((starRingEnd ℂ) c * (w - v)).re) * gw ε v w := rfl
  rw [this]
  exact ((continuous_const.mul (Complex.continuous_re.comp
    (continuous_const.mul (continuous_id.sub continuous_const))))).mul h

/- English proof (translation)
Establish `h` using `gw_cont ε v`. Establish `: G2 ε v c = fun w => (-2 * Real.pi * ε ^ 2 * ‖c‖ ^ 2 + 4 * Real.pi ^ 2 * ε ^ 4 * (((starRingEnd ℂ) c * (w - v)).re) ^ 2) * gw ε v w` using `rfl`. Rewrite using `[this]`. Conclude with `(continuous_const.add (continuous_const.mul ((Complex.continuous_re.comp (continuous_const.mul (continuous_id.sub continuous_const))).pow 2))).mul h`.
-/
lemma continuous_secondGaussDeriv (ε : ℝ) (v c : ℂ) : Continuous (G2 ε v c) := by
  have h := gw_cont ε v
  have : G2 ε v c = fun w => (-2 * Real.pi * ε ^ 2 * ‖c‖ ^ 2 + 4 * Real.pi ^ 2 * ε ^ 4 *
      (((starRingEnd ℂ) c * (w - v)).re) ^ 2) * gw ε v w := rfl
  rw [this]
  exact (continuous_const.add (continuous_const.mul ((Complex.continuous_re.comp
    (continuous_const.mul (continuous_id.sub continuous_const))).pow 2))).mul h

/- English proof (translation)
Use `(Complex.abs_re_le_norm _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_conj]`.
-/
lemma re_le (c u : ℂ) : |((starRingEnd ℂ) c * u).re| ≤ ‖c‖ * ‖u‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_conj]

/- English proof (translation)
The claim follows from `|G1 ε v c w| ≤ 2 * Real.pi * ε * ‖c‖ * Kf (ε • (w - v)) := by rw [Ks_eq ε hε] have hg := gw_pos ε v w have hr := re_le c (w - v) have hpi := Real.pi_pos set r := ((starRingEnd ℂ) c * (w - v)).re with hrdef set u := ‖w - v‖ with hu have hu0 : 0 ≤ u := norm_nonneg _ have hc0 : 0 ≤ …`.
-/
lemma firstGaussDeriv_bound (ε : ℝ) (hε : 0 < ε) (v c w : ℂ) :
    |G1 ε v c w| ≤ 2 * Real.pi * ε * ‖c‖ * Kf (ε • (w - v)) := by
  rw [Ks_eq ε hε]
  have hg := gw_pos ε v w
  have hr := re_le c (w - v)
  have hpi := Real.pi_pos
  set r := ((starRingEnd ℂ) c * (w - v)).re with hrdef
  set u := ‖w - v‖ with hu
  have hu0 : 0 ≤ u := norm_nonneg _
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg _
  have e : |G1 ε v c w| = 2 * Real.pi * ε ^ 2 * |r| * gw ε v w := by
    unfold G1
    rw [abs_mul, abs_mul, abs_of_pos hg, abs_of_nonpos (a := -2 * Real.pi * ε ^ 2)]
    · ring
    · have : 0 ≤ 2 * Real.pi * ε ^ 2 := by positivity
      linarith
  rw [e]
  have hx : ε * u ≤ 1 + (ε * u) ^ 2 := by nlinarith [sq_nonneg (ε * u - 1)]
  have h1 : 2 * Real.pi * ε ^ 2 * |r| ≤ 2 * Real.pi * ε * ‖c‖ * (1 + (ε * u) ^ 2) := by
    calc 2 * Real.pi * ε ^ 2 * |r| ≤ 2 * Real.pi * ε ^ 2 * (‖c‖ * u) := by gcongr
      _ = 2 * Real.pi * ε * ‖c‖ * (ε * u) := by ring
      _ ≤ 2 * Real.pi * ε * ‖c‖ * (1 + (ε * u) ^ 2) := by gcongr
  calc 2 * Real.pi * ε ^ 2 * |r| * gw ε v w
      ≤ (2 * Real.pi * ε * ‖c‖ * (1 + (ε * u) ^ 2)) * gw ε v w := by gcongr
    _ = 2 * Real.pi * ε * ‖c‖ * ((1 + (ε * u) ^ 2) * gw ε v w) := by ring

/- English proof (translation)
Use polynomial arithmetic with `[Real.pi_gt_three]`.
-/
lemma two_pi_le : 2 * Real.pi ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]

/- English proof (translation)
The claim follows from `|G2 ε v c w| ≤ 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 * Kf (ε • (w - v)) := by rw [Ks_eq ε hε] have hg := gw_pos ε v w have hr := re_le c (w - v) have hpi := Real.pi_pos set r := ((starRingEnd ℂ) c * (w - v)).re with hrdef set u := ‖w - v‖ with hu have hu0 : 0 ≤ u := norm_nonneg _ hav …`.
-/
lemma secondGaussDeriv_bound (ε : ℝ) (hε : 0 < ε) (v c w : ℂ) :
    |G2 ε v c w| ≤ 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 * Kf (ε • (w - v)) := by
  rw [Ks_eq ε hε]
  have hg := gw_pos ε v w
  have hr := re_le c (w - v)
  have hpi := Real.pi_pos
  set r := ((starRingEnd ℂ) c * (w - v)).re with hrdef
  set u := ‖w - v‖ with hu
  have hu0 : 0 ≤ u := norm_nonneg _
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg _
  have hr2 : r ^ 2 ≤ ‖c‖ ^ 2 * u ^ 2 := by
    rw [← mul_pow, ← sq_abs r]
    exact pow_le_pow_left₀ (abs_nonneg r) hr 2
  have e : |G2 ε v c w| = |-2 * Real.pi * ε ^ 2 * ‖c‖ ^ 2 + 4 * Real.pi ^ 2 * ε ^ 4 * r ^ 2| * gw ε v w := by
    unfold G2
    rw [abs_mul, abs_of_pos hg]
  rw [e]
  have h1 : |-2 * Real.pi * ε ^ 2 * ‖c‖ ^ 2 + 4 * Real.pi ^ 2 * ε ^ 4 * r ^ 2|
      ≤ 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 * (1 + (ε * u) ^ 2) := by
    have a : 0 ≤ 2 * Real.pi * ε ^ 2 * ‖c‖ ^ 2 := by positivity
    have b : 0 ≤ 4 * Real.pi ^ 2 * ε ^ 4 * r ^ 2 := by positivity
    have c1 : 2 * Real.pi * ε ^ 2 * ‖c‖ ^ 2 ≤ 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right two_pi_le (by positivity : 0 ≤ ε ^ 2 * ‖c‖ ^ 2)
      linarith
    have c2 : 4 * Real.pi ^ 2 * ε ^ 4 * r ^ 2 ≤ 4 * Real.pi ^ 2 * ε ^ 4 * (‖c‖ ^ 2 * u ^ 2) := by
      gcongr
    have e2 : 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 * (1 + (ε * u) ^ 2)
        = 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 + 4 * Real.pi ^ 2 * ε ^ 4 * (‖c‖ ^ 2 * u ^ 2) := by ring
    rw [e2, abs_le]
    constructor <;> linarith
  calc _ ≤ (4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 * (1 + (ε * u) ^ 2)) * gw ε v w := by gcongr
    _ = 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 * ((1 + (ε * u) ^ 2) * gw ε v w) := by ring

/- English proof (translation)
Use `set I : ℝ := ∫ w, Kf w with hI`. Establish `hI0 : 0 ≤ I` using `integral_nonneg Kf_nonneg`. Establish `hP : 0 < 4 * Real.pi ^ 2` using `by have := Real.pi_pos; positivity`. Establish `hP2` using `two_pi_le`. Establish `h2P : 0 < 2 * Real.pi` using `by have := Real.pi_pos; positivity`.

Use `⟨4 * Real.pi ^ 2 * (216 + I), by positivity, fun ε hε hε1 v c => ?_⟩` and prove the remaining obligations. Establish `hc0 : 0 ≤ ‖c‖` using `norm_nonneg _`. Establish `hB1 : 4 * Real.pi ^ 2 * 216 ≤ 4 * Real.pi ^ 2 * (216 + I)` using `by gcongr; linarith`. Establish `hB2 : 4 * Real.pi ^ 2 * I ≤ 4 * Real.pi ^ 2 * (216 + I)` using `by gcongr; linarith`. Establish `hB3 : 2 * Real.pi * I ≤ 4 * Real.pi ^ 2 * I` using `by gcongr`.

Establish `hB4 : 2 * Real.pi * 216 ≤ 4 * Real.pi ^ 2 * 216` using `by gcongr`. Establish `hK` using `Ks_int ε hε v`. Establish `hKI` using `Ks_integral ε hε v`. Establish `hi1 : Integrable (fun w => |G1 ε v c w|)` using `(hK.const_mul (2 * Real.pi * ε * ‖c‖)).mono' (continuous_firstGaussDeriv ε v c).abs.aestronglyMeasurable (Eventually.of_forall fun w => by`. Rewrite using `[Real.norm_of_nonneg (abs_nonneg _)]`.

Conclude with `firstGaussDeriv_bound ε hε v c w)`. Establish `hi2 : Integrable (fun w => |G2 ε v c w|)` using `(hK.const_mul (4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2)).mono' (continuous_secondGaussDeriv ε v c).abs.aestronglyMeasurable (Eventually.of_forall fun w => by`. Rewrite using `[Real.norm_of_nonneg (abs_nonneg _)]`. Conclude with `secondGaussDeriv_bound ε hε v c w)`. Use `⟨fun w => ⟨(gw_pos ε v w).le, gw_le ε v w⟩, gw_cont ε v, continuous_firstGaussDeriv ε v c, continuous_secondGaussDeriv ε v c, fun w => ?_, fun w => ?_, hi1, ?_, hi2, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `he : ε ^ 2 ≤ 1` using `pow_le_one₀ hε.le hε1`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : (∫ w, |G1 ε v c w|) ≤ ∫ w, 2 * Real.pi * ε * ‖c‖ * Kf (ε • (w - v))` using `integral_mono hi1 (hK.const_mul _) (fun w => firstGaussDeriv_bound ε hε v c w)`. Rewrite `h1` using `[integral_const_mul, hKI, ← hI]`.

Use `h1.trans (le_of_eq_of_le ?_ (?_ : (2 * Real.pi * I) * ‖c‖ / ε ≤ _))` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : (∫ w, |G2 ε v c w|) ≤ ∫ w, 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 * Kf (ε • (w - v))` using `integral_mono hi2 (hK.const_mul _) (fun w => secondGaussDeriv_bound ε hε v c w)`.

Rewrite `h1` using `[integral_const_mul, hKI, ← hI]`. Use `h1.trans (le_of_eq_of_le ?_ (?_ : (4 * Real.pi ^ 2 * I) * ‖c‖ ^ 2 ≤ _))` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Use `gcongr`.
-/
theorem main : ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ v c : ℂ,
    (∀ w, 0 ≤ gw ε v w ∧ gw ε v w ≤ 1) ∧ Continuous (gw ε v) ∧ Continuous (G1 ε v c) ∧ Continuous (G2 ε v c) ∧
    (∀ w, |G1 ε v c w| ≤ B * ε * ‖c‖) ∧ (∀ w, |G2 ε v c w| ≤ B * ‖c‖ ^ 2) ∧
    Integrable (fun w => |G1 ε v c w|) ∧ (∫ w, |G1 ε v c w|) ≤ B * ‖c‖ / ε ∧
    Integrable (fun w => |G2 ε v c w|) ∧ (∫ w, |G2 ε v c w|) ≤ B * ‖c‖ ^ 2 := by
  set I : ℝ := ∫ w, Kf w with hI
  have hI0 : 0 ≤ I := integral_nonneg Kf_nonneg
  have hP : 0 < 4 * Real.pi ^ 2 := by have := Real.pi_pos; positivity
  have hP2 := two_pi_le
  have h2P : 0 < 2 * Real.pi := by have := Real.pi_pos; positivity
  refine ⟨4 * Real.pi ^ 2 * (216 + I), by positivity, fun ε hε hε1 v c => ?_⟩
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg _
  have hB1 : 4 * Real.pi ^ 2 * 216 ≤ 4 * Real.pi ^ 2 * (216 + I) := by gcongr; linarith
  have hB2 : 4 * Real.pi ^ 2 * I ≤ 4 * Real.pi ^ 2 * (216 + I) := by gcongr; linarith
  have hB3 : 2 * Real.pi * I ≤ 4 * Real.pi ^ 2 * I := by gcongr
  have hB4 : 2 * Real.pi * 216 ≤ 4 * Real.pi ^ 2 * 216 := by gcongr
  have hK := Ks_int ε hε v
  have hKI := Ks_integral ε hε v
  have hi1 : Integrable (fun w => |G1 ε v c w|) :=
    (hK.const_mul (2 * Real.pi * ε * ‖c‖)).mono' (continuous_firstGaussDeriv ε v c).abs.aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (abs_nonneg _)]; exact firstGaussDeriv_bound ε hε v c w)
  have hi2 : Integrable (fun w => |G2 ε v c w|) :=
    (hK.const_mul (4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2)).mono' (continuous_secondGaussDeriv ε v c).abs.aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_of_nonneg (abs_nonneg _)]; exact secondGaussDeriv_bound ε hε v c w)
  refine ⟨fun w => ⟨(gw_pos ε v w).le, gw_le ε v w⟩, gw_cont ε v, continuous_firstGaussDeriv ε v c, continuous_secondGaussDeriv ε v c,
    fun w => ?_, fun w => ?_, hi1, ?_, hi2, ?_⟩
  · calc |G1 ε v c w| ≤ 2 * Real.pi * ε * ‖c‖ * Kf (ε • (w - v)) := firstGaussDeriv_bound ε hε v c w
      _ ≤ 2 * Real.pi * ε * ‖c‖ * 216 := by gcongr; exact Kf_le _
      _ = (2 * Real.pi * 216) * ε * ‖c‖ := by ring
      _ ≤ (4 * Real.pi ^ 2 * (216 + I)) * ε * ‖c‖ := by gcongr; linarith
  · have he : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le hε1
    calc |G2 ε v c w| ≤ 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 * Kf (ε • (w - v)) := secondGaussDeriv_bound ε hε v c w
      _ ≤ 4 * Real.pi ^ 2 * 1 * ‖c‖ ^ 2 * 216 :=
          mul_le_mul (by gcongr) (Kf_le _) (Kf_nonneg _) (by positivity)
      _ = (4 * Real.pi ^ 2 * 216) * ‖c‖ ^ 2 := by ring
      _ ≤ (4 * Real.pi ^ 2 * (216 + I)) * ‖c‖ ^ 2 := by gcongr
  · have h1 : (∫ w, |G1 ε v c w|) ≤ ∫ w, 2 * Real.pi * ε * ‖c‖ * Kf (ε • (w - v)) :=
      integral_mono hi1 (hK.const_mul _) (fun w => firstGaussDeriv_bound ε hε v c w)
    rw [integral_const_mul, hKI, ← hI] at h1
    refine h1.trans (le_of_eq_of_le ?_ (?_ : (2 * Real.pi * I) * ‖c‖ / ε ≤ _))
    · field_simp
    · gcongr
      linarith
  · have h1 : (∫ w, |G2 ε v c w|) ≤ ∫ w, 4 * Real.pi ^ 2 * ε ^ 2 * ‖c‖ ^ 2 * Kf (ε • (w - v)) :=
      integral_mono hi2 (hK.const_mul _) (fun w => secondGaussDeriv_bound ε hε v c w)
    rw [integral_const_mul, hKI, ← hI] at h1
    refine h1.trans (le_of_eq_of_le ?_ (?_ : (4 * Real.pi ^ 2 * I) * ‖c‖ ^ 2 ≤ _))
    · field_simp
    · gcongr

end GlobalTheory.CompanionTheory.ParsC.GaussB
