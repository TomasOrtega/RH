import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.DensDefs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisMore

noncomputable section

open MeasureTheory

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

/- English proof (translation)
The claim follows from `(norm_le_pi_norm (x a) i).trans (norm_le_pi_norm x a)`.
-/
theorem norm_coord_le (x : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) : ‖x a i‖ ≤ ‖x‖ :=
  (norm_le_pi_norm (x a) i).trans (norm_le_pi_norm x a)

/- English proof (translation)
Unfold `evX`. Establish `hg : Continuous fun x : Fin m → Fin n → ℂ => (fun k : Fin m × Fin n × Bool => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1)`. Use `continuous_pi fun k => ?_` and prove the remaining obligations. Distinguish the cases in `h : k.2.2`. Simplify using `only [h, if_true]`.

Conclude with `continuous_star.comp ((continuous_apply _).comp (continuous_apply _))`. Simplify using `only [h, if_false, Bool.false_eq_true]`. Conclude with `(continuous_apply _).comp (continuous_apply _)`. Conclude with `(MvPolynomial.continuous_eval P).comp hg`.
-/
theorem continuous_evXI (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x := by
  unfold evX
  have hg : Continuous fun x : Fin m → Fin n → ℂ =>
      (fun k : Fin m × Fin n × Bool => if k.2.2 then star (x k.1 k.2.1) else x k.1 k.2.1) := by
    refine continuous_pi fun k => ?_
    by_cases h : k.2.2
    · simp only [h, if_true]
      exact continuous_star.comp ((continuous_apply _).comp (continuous_apply _))
    · simp only [h, if_false, Bool.false_eq_true]
      exact (continuous_apply _).comp (continuous_apply _)
  exact (MvPolynomial.continuous_eval P).comp hg

/- English proof (translation)
Unfold `gs`. Use `fun_prop`.
-/
theorem continuous_gs (c : ℝ) : Continuous fun x : Fin m → Fin n → ℂ => gs c x := by
  unfold gs
  fun_prop

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => exact ⟨‖a‖, 0, fun x => by simp [evX]⟩`. Consider the case `add p q hp hq`. Take `⟨C1, d1, h1⟩` from `hp`. Take `⟨C2, d2, h2⟩` from `hq`.

Use `⟨|C1| + |C2|, d1 + d2, fun x => ?_⟩` and prove the remaining obligations. Establish `h0 : (1 : ℝ) ≤ 1 + ‖x‖` using `by linarith [norm_nonneg x]`. Establish `e1 : (1 + ‖x‖) ^ d1 ≤ (1 + ‖x‖) ^ (d1 + d2)` using `pow_le_pow_right₀ h0 (by omega)`. Establish `e2 : (1 + ‖x‖) ^ d2 ≤ (1 + ‖x‖) ^ (d1 + d2)` using `pow_le_pow_right₀ h0 (by omega)`. Establish `f1 : C1 * (1 + ‖x‖) ^ d1 ≤ |C1| * (1 + ‖x‖) ^ (d1 + d2)` using `(mul_le_mul_of_nonneg_right (le_abs_self C1) (by positivity)).trans (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))`.

Establish `f2 : C2 * (1 + ‖x‖) ^ d2 ≤ |C2| * (1 + ‖x‖) ^ (d1 + d2)` using `(mul_le_mul_of_nonneg_right (le_abs_self C2) (by positivity)).trans (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [evX, map_add]`. Conclude with `norm_add_le _ _`. Use `_ ≤ C1 * (1 + ‖x‖) ^ d1 + C2 * (1 + ‖x‖) ^ d2 := add_le_add (h1 x) (h2 x)`.

Use `_ ≤ |C1| * (1 + ‖x‖) ^ (d1 + d2) + |C2| * (1 + ‖x‖) ^ (d1 + d2) := add_le_add f1 f2`. Use `_ = (|C1| + |C2|) * (1 + ‖x‖) ^ (d1 + d2) := by ring`. Consider the case `mul_X p v hp`. Take `⟨C, d, h⟩` from `hp`. Use `⟨|C|, d + 1, fun x => ?_⟩` and prove the remaining obligations.

Establish `hv : ‖(if v.2.2 then star (x v.1 v.2.1) else x v.1 v.2.1)‖ ≤ 1 + ‖x‖`. Use `norm_coord_le x v.1 v.2.1` as an intermediate fact. Apply the tactic sequence `by_cases hb : v.2.2 <;> simp [hb] <;> linarith`. Establish `hC : ‖evX p x‖ ≤ |C| * (1 + ‖x‖) ^ d` using `(h x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))`. Combine the equalities or inequalities in the displayed calculation.

Apply the tactic sequence `by_cases hb : v.2.2 <;> simp [evX, hb]`. Use `_ ≤ (|C| * (1 + ‖x‖) ^ d) * (1 + ‖x‖) := mul_le_mul hC hv (norm_nonneg _) (by positivity)`. Use `_ = |C| * (1 + ‖x‖) ^ (d + 1) := by ring`.
-/
theorem evX_bound (P : PX m n) : ∃ (C : ℝ) (d : ℕ), ∀ x : Fin m → Fin n → ℂ, ‖evX P x‖ ≤ C * (1 + ‖x‖) ^ d := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, fun x => by simp [evX]⟩
  | add p q hp hq =>
    obtain ⟨C1, d1, h1⟩ := hp
    obtain ⟨C2, d2, h2⟩ := hq
    refine ⟨|C1| + |C2|, d1 + d2, fun x => ?_⟩
    have h0 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have e1 : (1 + ‖x‖) ^ d1 ≤ (1 + ‖x‖) ^ (d1 + d2) := pow_le_pow_right₀ h0 (by omega)
    have e2 : (1 + ‖x‖) ^ d2 ≤ (1 + ‖x‖) ^ (d1 + d2) := pow_le_pow_right₀ h0 (by omega)
    have f1 : C1 * (1 + ‖x‖) ^ d1 ≤ |C1| * (1 + ‖x‖) ^ (d1 + d2) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C1) (by positivity)).trans
        (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
    have f2 : C2 * (1 + ‖x‖) ^ d2 ≤ |C2| * (1 + ‖x‖) ^ (d1 + d2) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C2) (by positivity)).trans
        (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
    calc ‖evX (p + q) x‖ ≤ ‖evX p x‖ + ‖evX q x‖ := by
          simp only [evX, map_add]; exact norm_add_le _ _
      _ ≤ C1 * (1 + ‖x‖) ^ d1 + C2 * (1 + ‖x‖) ^ d2 := add_le_add (h1 x) (h2 x)
      _ ≤ |C1| * (1 + ‖x‖) ^ (d1 + d2) + |C2| * (1 + ‖x‖) ^ (d1 + d2) := add_le_add f1 f2
      _ = (|C1| + |C2|) * (1 + ‖x‖) ^ (d1 + d2) := by ring
  | mul_X p v hp =>
    obtain ⟨C, d, h⟩ := hp
    refine ⟨|C|, d + 1, fun x => ?_⟩
    have hv : ‖(if v.2.2 then star (x v.1 v.2.1) else x v.1 v.2.1)‖ ≤ 1 + ‖x‖ := by
      have := norm_coord_le x v.1 v.2.1
      by_cases hb : v.2.2 <;> simp [hb] <;> linarith
    have hC : ‖evX p x‖ ≤ |C| * (1 + ‖x‖) ^ d :=
      (h x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    calc ‖evX (p * MvPolynomial.X v) x‖
        = ‖evX p x‖ * ‖(if v.2.2 then star (x v.1 v.2.1) else x v.1 v.2.1)‖ := by
          by_cases hb : v.2.2 <;> simp [evX, hb]
      _ ≤ (|C| * (1 + ‖x‖) ^ d) * (1 + ‖x‖) := mul_le_mul hC hv (norm_nonneg _) (by positivity)
      _ = |C| * (1 + ‖x‖) ^ (d + 1) := by ring

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.DYka1.main x`.
-/
theorem sq_norm_le_sum (x : Fin m → Fin n → ℂ) : ‖x‖ ^ 2 ≤ ∑ a, ∑ i, ‖x a i‖ ^ 2 :=
  _root_.UpperTheory.Reformulated.B.DYka1.main x

/- English proof (translation)
Unfold `gs`. Rewrite using `[← Complex.ofReal_neg, Complex.norm_exp_ofReal]`. Conclude with `Real.exp_le_exp.2 (by nlinarith [sq_norm_le_sum x])`.
-/
theorem norm_gs_le (c : ℝ) (hc : 0 < c) (x : Fin m → Fin n → ℂ) : ‖gs c x‖ ≤ Real.exp (-(c * ‖x‖ ^ 2)) := by
  unfold gs
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
  exact Real.exp_le_exp.2 (by nlinarith [sq_norm_le_sum x])

/- English proof (translation)
Use `⟨4 ^ k * (1 + (k.factorial : ℝ) / c ^ k), fun s hs => ?_⟩` and prove the remaining obligations. Establish `hpow : (1 + s) ^ (2 * k) ≤ 4 ^ k * (1 + s ^ (2 * k))`. Break down `le_total s 1 with h | h` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Establish `: 0 ≤ s ^ (2 * k)` using `by positivity`.

Use polynomial arithmetic with `[pow_pos (by norm_num : (0:ℝ) < 4) k]`. Combine the equalities or inequalities in the displayed calculation. Establish `: 0 ≤ (4:ℝ) ^ k` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hexp : s ^ (2 * k) ≤ (k.factorial : ℝ) / c ^ k * Real.exp (c * s ^ 2)`.

Establish `h1` using `Real.pow_div_factorial_le_exp (c * s ^ 2) (by positivity) k`. Establish `hck : 0 < c ^ k` using `pow_pos hc k`. Establish `hf : (0 : ℝ) < k.factorial` using `by exact_mod_cast Nat.factorial_pos k`. Rewrite `h1` using `[div_le_iff₀ hf]`. Rewrite using `[pow_mul, div_mul_eq_mul_div, le_div_iff₀ hck]`.

Combine the equalities or inequalities in the displayed calculation. Establish `he : 0 < Real.exp (-(c * s ^ 2))` using `Real.exp_pos _`. Establish `hee : Real.exp (c * s ^ 2) * Real.exp (-(c * s ^ 2)) = 1`. Rewrite using `[← Real.exp_add]`. Simplify using the standard rewrite rules.

Establish `h1le : 1 ≤ Real.exp (c * s ^ 2)` using `Real.one_le_exp (by positivity)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem decay (c : ℝ) (hc : 0 < c) (k : ℕ) : ∃ K : ℝ, ∀ s : ℝ, 0 ≤ s → (1 + s) ^ (2 * k) * Real.exp (-(c * s ^ 2)) ≤ K := by
  refine ⟨4 ^ k * (1 + (k.factorial : ℝ) / c ^ k), fun s hs => ?_⟩
  have hpow : (1 + s) ^ (2 * k) ≤ 4 ^ k * (1 + s ^ (2 * k)) := by
    rcases le_total s 1 with h | h
    · calc (1 + s) ^ (2 * k) ≤ 2 ^ (2 * k) := pow_le_pow_left₀ (by linarith) (by linarith) _
        _ = 4 ^ k := by rw [pow_mul]; norm_num
        _ ≤ 4 ^ k * (1 + s ^ (2 * k)) := by
          have : 0 ≤ s ^ (2 * k) := by positivity
          nlinarith [pow_pos (by norm_num : (0:ℝ) < 4) k]
    · calc (1 + s) ^ (2 * k) ≤ (2 * s) ^ (2 * k) := pow_le_pow_left₀ (by linarith) (by linarith) _
        _ = 4 ^ k * s ^ (2 * k) := by rw [mul_pow, pow_mul]; norm_num
        _ ≤ 4 ^ k * (1 + s ^ (2 * k)) := by
          have : 0 ≤ (4:ℝ) ^ k := by positivity
          nlinarith
  have hexp : s ^ (2 * k) ≤ (k.factorial : ℝ) / c ^ k * Real.exp (c * s ^ 2) := by
    have h1 := Real.pow_div_factorial_le_exp (c * s ^ 2) (by positivity) k
    have hck : 0 < c ^ k := pow_pos hc k
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [div_le_iff₀ hf] at h1
    rw [pow_mul, div_mul_eq_mul_div, le_div_iff₀ hck]
    calc (s ^ 2) ^ k * c ^ k = (c * s ^ 2) ^ k := by ring
      _ ≤ Real.exp (c * s ^ 2) * k.factorial := h1
      _ = k.factorial * Real.exp (c * s ^ 2) := by ring
  have he : 0 < Real.exp (-(c * s ^ 2)) := Real.exp_pos _
  have hee : Real.exp (c * s ^ 2) * Real.exp (-(c * s ^ 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have h1le : 1 ≤ Real.exp (c * s ^ 2) := Real.one_le_exp (by positivity)
  calc (1 + s) ^ (2 * k) * Real.exp (-(c * s ^ 2))
      ≤ 4 ^ k * (1 + s ^ (2 * k)) * Real.exp (-(c * s ^ 2)) := mul_le_mul_of_nonneg_right hpow he.le
    _ ≤ 4 ^ k * (Real.exp (c * s ^ 2) + (k.factorial : ℝ) / c ^ k * Real.exp (c * s ^ 2)) *
          Real.exp (-(c * s ^ 2)) := by gcongr
    _ = 4 ^ k * (1 + (k.factorial : ℝ) / c ^ k) * (Real.exp (c * s ^ 2) * Real.exp (-(c * s ^ 2))) := by ring
    _ = 4 ^ k * (1 + (k.factorial : ℝ) / c ^ k) := by rw [hee, mul_one]

instance haarNested (m n : ℕ) : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := by
  have : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := inferInstance
  have : SigmaFinite (volume : Measure (Fin n → ℂ)) := inferInstance
  exact Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite

/- English proof (translation)
Introduce `m n c hc P`. Take `⟨C, d, hP⟩` from `evX_bound P`. Use `set r : ℕ := Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 with hr`. Take `⟨K, hK⟩` from `decay c hc (d + r)`. Establish `hint : Integrable (fun x : Fin m → Fin n → ℂ => (1 + ‖x‖) ^ (-(r : ℝ)))` using `integrable_one_add_norm (by rw [hr]; push_cast; linarith)`.

Use `(hint.const_mul (|C| * K)).mono' ((continuous_evXI P).mul (continuous_gs c)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Establish `h1 : (1 : ℝ) ≤ 1 + ‖x‖` using `by linarith [norm_nonneg x]`. Establish `hpos : 0 < 1 + ‖x‖` using `by linarith`. Establish `hK' : (1 + ‖x‖) ^ (d + r) * Real.exp (-(c * ‖x‖ ^ 2)) ≤ K` using `(mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 (by omega)) (Real.exp_pos _).le).trans (hK ‖x‖ (norm_nonneg x))`. Establish `hrp : (1 + ‖x‖) ^ (-(r : ℝ)) = ((1 + ‖x‖) ^ r)⁻¹`.

Rewrite using `[Real.rpow_neg hpos.le, Real.rpow_natCast]`. Establish `hPx : ‖evX P x‖ ≤ |C| * (1 + ‖x‖) ^ d` using `(hP x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))`. Establish `hr0 : 0 < (1 + ‖x‖) ^ r` using `pow_pos hpos r`. Rewrite using `[norm_mul, hrp]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[pow_add]`. Clear the denominators using the available nonvanishing facts. Use `_ ≤ |C| * K * ((1 + ‖x‖) ^ r)⁻¹ := by gcongr`.
-/
theorem intG : IntG := by
  intro m n c hc P
  obtain ⟨C, d, hP⟩ := evX_bound P
  set r : ℕ := Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 with hr
  obtain ⟨K, hK⟩ := decay c hc (d + r)
  have hint : Integrable (fun x : Fin m → Fin n → ℂ => (1 + ‖x‖) ^ (-(r : ℝ))) :=
    integrable_one_add_norm (by rw [hr]; push_cast; linarith)
  refine (hint.const_mul (|C| * K)).mono' ((continuous_evXI P).mul (continuous_gs c)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hpos : 0 < 1 + ‖x‖ := by linarith
  have hK' : (1 + ‖x‖) ^ (d + r) * Real.exp (-(c * ‖x‖ ^ 2)) ≤ K :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 (by omega)) (Real.exp_pos _).le).trans
      (hK ‖x‖ (norm_nonneg x))
  have hrp : (1 + ‖x‖) ^ (-(r : ℝ)) = ((1 + ‖x‖) ^ r)⁻¹ := by
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
  have hPx : ‖evX P x‖ ≤ |C| * (1 + ‖x‖) ^ d :=
    (hP x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have hr0 : 0 < (1 + ‖x‖) ^ r := pow_pos hpos r
  rw [norm_mul, hrp]
  calc ‖evX P x‖ * ‖gs c x‖ ≤ (|C| * (1 + ‖x‖) ^ d) * Real.exp (-(c * ‖x‖ ^ 2)) :=
        mul_le_mul hPx (norm_gs_le c hc x) (norm_nonneg _) (by positivity)
    _ = |C| * ((1 + ‖x‖) ^ (d + r) * Real.exp (-(c * ‖x‖ ^ 2))) * ((1 + ‖x‖) ^ r)⁻¹ := by
        rw [pow_add]; field_simp
    _ ≤ |C| * K * ((1 + ‖x‖) ^ r)⁻¹ := by
        gcongr

end PositivityTheory.Rg.Sw.WR.D
