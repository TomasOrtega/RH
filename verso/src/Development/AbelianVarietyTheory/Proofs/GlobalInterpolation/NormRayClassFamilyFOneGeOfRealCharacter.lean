import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpSumBoundsStatement
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

noncomputable section

namespace GlobalTheory.Hk.RealChar

def kerW (y w : ℝ) : ℝ := Real.exp (-(y / w)) * Real.exp (-w) / w

def besW (y : ℝ) : ℝ := ∫ w in Set.Ioi (0 : ℝ), kerW y w

/- English proof (translation)
Unfold `kerW`. Check the signs of the components of the expression.
-/
lemma kerW_pos (y : ℝ) {w : ℝ} (hw : 0 < w) : 0 < kerW y w := by
  unfold kerW; positivity

/- English proof (translation)
Establish `h` using `Real.pow_div_factorial_le_exp (y / w) (by positivity) 3`. Establish `h3 : w ^ ((3 : ℝ) - 1) = w ^ 2`. Rewrite using `[show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Establish `h1 : Real.exp (-(y / w)) ≤ 6 * w ^ 3 / y ^ 3`. Rewrite using `[Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]`.

Use `le_trans (le_of_eq ?_) h` and prove the remaining obligations. Simplify using `only [Nat.factorial]`. Clear the denominators using the available nonvanishing facts. Evaluate the numerical expressions. Rewrite using `[h3]`.

Unfold `kerW`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma kerW_le {y w : ℝ} (hy : 0 < y) (hw : 0 < w) :
    kerW y w ≤ 6 / y ^ 3 * (Real.exp (-w) * w ^ ((3 : ℝ) - 1)) := by
  have h := Real.pow_div_factorial_le_exp (y / w) (by positivity) 3
  have h3 : w ^ ((3 : ℝ) - 1) = w ^ 2 := by
    rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h1 : Real.exp (-(y / w)) ≤ 6 * w ^ 3 / y ^ 3 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
    refine le_trans (le_of_eq ?_) h
    simp only [Nat.factorial]
    field_simp
    norm_num
  rw [h3]
  unfold kerW
  calc Real.exp (-(y / w)) * Real.exp (-w) / w ≤ 6 * w ^ 3 / y ^ 3 * Real.exp (-w) / w := by
        gcongr
    _ = _ := by field_simp

/- English proof (translation)
Unfold `kerW`. Use `fun_prop`.
-/
lemma measurable_kerW (y : ℝ) : Measurable (kerW y) := by
  unfold kerW; fun_prop

/- English proof (translation)
Use `Integrable.mono' ((Real.GammaIntegral_convergent (s := 3) (by norm_num)).const_mul (6 / y ^ 3)) (measurable_kerW y).aestronglyMeasurable ?_` and prove the remaining obligations. Use `(ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_of_nonneg (kerW_pos y hw).le]`. Conclude with `kerW_le hy hw`.
-/
lemma integrableOn_kerW {y : ℝ} (hy : 0 < y) : IntegrableOn (kerW y) (Set.Ioi 0) := by
  refine Integrable.mono' ((Real.GammaIntegral_convergent (s := 3) (by norm_num)).const_mul (6 / y ^ 3))
    (measurable_kerW y).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
  rw [Real.norm_of_nonneg (kerW_pos y hw).le]
  exact kerW_le hy hw

/- English proof (translation)
The claim follows from `setIntegral_nonneg measurableSet_Ioi fun _ hw => (kerW_pos y hw).le`.
-/
lemma besW_nonneg (y : ℝ) : 0 ≤ besW y :=
  setIntegral_nonneg measurableSet_Ioi fun _ hw => (kerW_pos y hw).le

/- English proof (translation)
Use `⟨6 * ∫ w in Set.Ioi (0 : ℝ), Real.exp (-w) * w ^ ((3 : ℝ) - 1), ?_, fun y hy => ?_⟩` and prove the remaining obligations. Use `mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi fun w hw => ?_)` and prove the remaining obligations. Establish `: 0 < w` using `hw`. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation.
-/
lemma besW_le : ∃ G : ℝ, 0 ≤ G ∧ ∀ y : ℝ, 0 < y → besW y ≤ G / y ^ 3 := by
  refine ⟨6 * ∫ w in Set.Ioi (0 : ℝ), Real.exp (-w) * w ^ ((3 : ℝ) - 1), ?_, fun y hy => ?_⟩
  · refine mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi fun w hw => ?_)
    have : 0 < w := hw
    positivity
  · calc besW y ≤ ∫ w in Set.Ioi (0 : ℝ), 6 / y ^ 3 * (Real.exp (-w) * w ^ ((3 : ℝ) - 1)) :=
          setIntegral_mono_on (integrableOn_kerW hy)
            ((Real.GammaIntegral_convergent (s := 3) (by norm_num)).const_mul (6 / y ^ 3))
            measurableSet_Ioi fun w hw => kerW_le hy hw
      _ = _ := by rw [integral_const_mul]; ring

/- English proof (translation)
Use `setIntegral_mono_on (integrableOn_kerW one_pos) (integrableOn_kerW hv) measurableSet_Ioi fun w hw => ?_` and prove the remaining obligations. Establish `: 0 < w` using `hw`. Unfold `kerW`. Use `gcongr`.
-/
lemma besW_one_le {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) : besW 1 ≤ besW v := by
  refine setIntegral_mono_on (integrableOn_kerW one_pos) (integrableOn_kerW hv)
    measurableSet_Ioi fun w hw => ?_
  have : 0 < w := hw
  unfold kerW
  gcongr

/- English proof (translation)
Unfold `besW`. Rewrite using `[setIntegral_pos_iff_support_of_nonneg_ae ?_ (integrableOn_kerW one_pos)]`. Establish `: Function.support (kerW 1) ∩ Set.Ioi 0 = Set.Ioi 0` using `Set.inter_eq_right.2 fun w hw => (kerW_pos 1 hw).ne'`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Conclude with `(ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => (kerW_pos 1 hw).le)`.
-/
lemma besW_one_pos : 0 < besW 1 := by
  unfold besW
  rw [setIntegral_pos_iff_support_of_nonneg_ae ?_ (integrableOn_kerW one_pos)]
  · have : Function.support (kerW 1) ∩ Set.Ioi 0 = Set.Ioi 0 :=
      Set.inter_eq_right.2 fun w hw => (kerW_pos 1 hw).ne'
    rw [this]; simp
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => (kerW_pos 1 hw).le)

/- English proof (translation)
Unfold `kerW`. Rewrite using `[mul_div_mul_right _ _ hn.ne']`. Clear the denominators using the available nonvanishing facts.
-/
lemma scale_eq (y : ℝ) {n w : ℝ} (hn : 0 < n) (hw : 0 < w) :
    Real.exp (-(y / w)) * Real.exp (-(w * n)) / w = n * kerW (y * n) (w * n) := by
  unfold kerW
  rw [mul_div_mul_right _ _ hn.ne']
  field_simp

/- English proof (translation)
Establish `h : IntegrableOn (fun w => kerW (y * n) (w * n)) (Set.Ioi 0)`. Rewrite using `[integrableOn_Ioi_comp_mul_right_iff (kerW (y * n)) 0 hn, zero_mul]`. Conclude with `integrableOn_kerW (by positivity)`. Conclude with `IntegrableOn.congr_fun (h.const_mul n) (fun w hw => (scale_eq y hn hw).symm) measurableSet_Ioi`.
-/
lemma scale_integrable {y n : ℝ} (hy : 0 < y) (hn : 0 < n) :
    IntegrableOn (fun w => Real.exp (-(y / w)) * Real.exp (-(w * n)) / w) (Set.Ioi 0) := by
  have h : IntegrableOn (fun w => kerW (y * n) (w * n)) (Set.Ioi 0) := by
    rw [integrableOn_Ioi_comp_mul_right_iff (kerW (y * n)) 0 hn, zero_mul]
    exact integrableOn_kerW (by positivity)
  exact IntegrableOn.congr_fun (h.const_mul n) (fun w hw => (scale_eq y hn hw).symm) measurableSet_Ioi

/- English proof (translation)
Rewrite using `[setIntegral_congr_fun measurableSet_Ioi (fun w hw => scale_eq y hn hw), integral_const_mul, integral_comp_mul_right_Ioi (kerW (y * n)) 0 hn, zero_mul, smul_eq_mul]`. Unfold `besW`. Clear the denominators using the available nonvanishing facts.
-/
lemma scale_integral (y : ℝ) {n : ℝ} (hn : 0 < n) :
    ∫ w in Set.Ioi (0 : ℝ), Real.exp (-(y / w)) * Real.exp (-(w * n)) / w = besW (y * n) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun w hw => scale_eq y hn hw), integral_const_mul,
    integral_comp_mul_right_Ioi (kerW (y * n)) 0 hn, zero_mul, smul_eq_mul]
  unfold besW
  field_simp

def th (a : ℕ → ℝ) (t : ℝ) : ℝ := ∑' n : ℕ, a n * Real.exp (-(t * n))

/- English proof (translation)
Unfold `th`. Conclude with `Measurable.tsum fun n => by fun_prop`.
-/
lemma measurable_th (a : ℕ → ℝ) : Measurable (th a) := by
  unfold th
  exact Measurable.tsum fun n => by fun_prop

/- English proof (translation)
Use `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) ((Real.summable_pow_mul_exp_neg_nat_mul 1 ht).mul_left D)` and prove the remaining obligations. Rewrite using `[norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le, pow_one, ← mul_assoc, neg_mul]`. Use `gcongr`. Conclude with `ha n`.
-/
lemma summable_th {a : ℕ → ℝ} {D : ℝ} (ha : ∀ n, |a n| ≤ D * n) {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℕ => ‖a n * Real.exp (-(t * n))‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((Real.summable_pow_mul_exp_neg_nat_mul 1 ht).mul_left D)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le, pow_one, ← mul_assoc, neg_mul]
  gcongr
  exact ha n

/- English proof (translation)
Establish `a0 : a 0 = 0` using `by simpa using ha 0`. Establish `b0 : b 0 = 0` using `by simpa using hb 0`. Establish `hD : 0 ≤ D` using `by simpa using (abs_nonneg _).trans (ha 1)`. Use `set f : ℕ × ℕ → ℝ → ℝ := fun p w => a p.1 * b p.2 * (Real.exp (-(v * p.1 / w)) * Real.exp (-(w * p.2)) / w) with hf`. Establish `hz : ∀ p : ℕ × ℕ, a p.1 * b p.2 = 0 ∨ (0 < p.1 ∧ 0 < p.2)`.

Introduce and unpack `⟨m, n⟩`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Use `left`. Simplify using `[a0]`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases.

Use `left`. Simplify using `[b0]`. Conclude with `Or.inr ⟨hm, hn⟩`. Establish `hint : ∀ p, Integrable (f p) (volume.restrict (Set.Ioi (0 : ℝ)))`. Introduce `p`.

Break down `hz p with h | ⟨h1, h2⟩` into its components or cases. Simplify using `[hf, h]`. Conclude with `(scale_integrable (y := v * p.1) (n := p.2) (by positivity) (by positivity)).const_mul _`. Establish `hval : ∀ p, ∫ w in Set.Ioi (0 : ℝ), f p w = a p.1 * b p.2 * besW (v * p.1 * p.2)`. Introduce `p`.

Break down `hz p with h | ⟨h1, h2⟩` into its components or cases. Simplify using `[hf, h]`. Simplify using `only [hf]`. Rewrite using `[integral_const_mul, scale_integral (v * p.1) (n := p.2) (by positivity)]`. Take `⟨G, hG0, hG⟩` from `besW_le`.

Establish `hs2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2` using `Real.summable_one_div_nat_pow.2 (by norm_num)`. Establish `hsum : Summable fun p => ∫ w in Set.Ioi (0 : ℝ), ‖f p w‖`. Use `Summable.of_nonneg_of_le (fun p => integral_nonneg fun w => norm_nonneg _) (fun p => ?_) ((hs2.mul_of_nonneg hs2 (fun n => by positivity) (fun n => by positivity)).mul_left (D * D * G / v ^ 3))` and prove the remaining obligations. Break down `hz p with h | ⟨h1, h2⟩` into its components or cases. Simplify using `only [hf, h, zero_mul, norm_zero, integral_zero]`.

Check the signs of the components of the expression. Establish `e : ∫ w in Set.Ioi (0 : ℝ), ‖f p w‖ = |a p.1| * |b p.2| * besW (v * p.1 * p.2)`. Rewrite using `[← scale_integral (v * p.1) (n := p.2) (by positivity), ← integral_const_mul]`. Use `setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_` and prove the remaining obligations. Establish `: 0 < w` using `hw`.

Simplify using `only [hf]`. Rewrite using `[norm_mul, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ Real.exp (-(v * p.1 / w)) * Real.exp (-(w * p.2)) / w)]`. Both sides reduce to the same expression. Rewrite using `[e]`. Establish `h1' : (0 : ℝ) < p.1` using `by positivity`.

Establish `h2' : (0 : ℝ) < p.2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Conclude with `besW_nonneg _`. Conclude with `ha _`. Conclude with `hb _`.

Conclude with `hG _ (by positivity)`. Use `_ = _ := by field_simp`. Establish `H` using `hasSum_integral_of_summable_integral_norm hint hsum`. Simplify using `only [hval] at H`. It suffices to establish `e : ∫ w in Set.Ioi (0 : ℝ), th a (v / w) * th b w / w = ∫ w in Set.Ioi (0 : ℝ), ∑' p, f p w by rw [e]; exact H`.

Use `setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_` and prove the remaining obligations. Establish `hw' : 0 < w` using `hw`. Simplify using `only [th]`. Rewrite using `[tsum_mul_tsum_of_summable_norm (summable_th ha (by positivity)) (summable_th hb hw'), ← tsum_div_const]`. Use `tsum_congr fun p => ?_` and prove the remaining obligations.

Simplify using `only [hf]`. Rewrite using `[show v / w * (p.1 : ℝ) = v * p.1 / w by ring]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hasSum_pairs {a b : ℕ → ℝ} {D : ℝ} (ha : ∀ n, |a n| ≤ D * n) (hb : ∀ n, |b n| ≤ D * n)
    {v : ℝ} (hv : 0 < v) :
    HasSum (fun p : ℕ × ℕ => a p.1 * b p.2 * besW (v * p.1 * p.2))
      (∫ w in Set.Ioi (0 : ℝ), th a (v / w) * th b w / w) := by
  have a0 : a 0 = 0 := by simpa using ha 0
  have b0 : b 0 = 0 := by simpa using hb 0
  have hD : 0 ≤ D := by simpa using (abs_nonneg _).trans (ha 1)
  set f : ℕ × ℕ → ℝ → ℝ := fun p w =>
    a p.1 * b p.2 * (Real.exp (-(v * p.1 / w)) * Real.exp (-(w * p.2)) / w) with hf
  have hz : ∀ p : ℕ × ℕ, a p.1 * b p.2 = 0 ∨ (0 < p.1 ∧ 0 < p.2) := by
    rintro ⟨m, n⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · left; simp [a0]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · left; simp [b0]
    exact Or.inr ⟨hm, hn⟩
  have hint : ∀ p, Integrable (f p) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro p
    rcases hz p with h | ⟨h1, h2⟩
    · simp [hf, h]
    · exact (scale_integrable (y := v * p.1) (n := p.2) (by positivity) (by positivity)).const_mul _
  have hval : ∀ p, ∫ w in Set.Ioi (0 : ℝ), f p w = a p.1 * b p.2 * besW (v * p.1 * p.2) := by
    intro p
    rcases hz p with h | ⟨h1, h2⟩
    · simp [hf, h]
    · simp only [hf]
      rw [integral_const_mul, scale_integral (v * p.1) (n := p.2) (by positivity)]
  obtain ⟨G, hG0, hG⟩ := besW_le
  have hs2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 := Real.summable_one_div_nat_pow.2 (by norm_num)
  have hsum : Summable fun p => ∫ w in Set.Ioi (0 : ℝ), ‖f p w‖ := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun w => norm_nonneg _) (fun p => ?_)
      ((hs2.mul_of_nonneg hs2 (fun n => by positivity) (fun n => by positivity)).mul_left
        (D * D * G / v ^ 3))
    rcases hz p with h | ⟨h1, h2⟩
    · simp only [hf, h, zero_mul, norm_zero, integral_zero]
      positivity
    · have e : ∫ w in Set.Ioi (0 : ℝ), ‖f p w‖ = |a p.1| * |b p.2| * besW (v * p.1 * p.2) := by
        rw [← scale_integral (v * p.1) (n := p.2) (by positivity), ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
        have : 0 < w := hw
        simp only [hf]
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ Real.exp (-(v * p.1 / w)) * Real.exp (-(w * p.2)) / w)]
        rfl
      rw [e]
      have h1' : (0 : ℝ) < p.1 := by positivity
      have h2' : (0 : ℝ) < p.2 := by positivity
      calc |a p.1| * |b p.2| * besW (v * p.1 * p.2)
          ≤ (D * p.1) * (D * p.2) * (G / (v * p.1 * p.2) ^ 3) := by
            gcongr
            · exact besW_nonneg _
            · exact ha _
            · exact hb _
            · exact hG _ (by positivity)
        _ = _ := by field_simp
  have H := hasSum_integral_of_summable_integral_norm hint hsum
  simp only [hval] at H
  suffices e : ∫ w in Set.Ioi (0 : ℝ), th a (v / w) * th b w / w
      = ∫ w in Set.Ioi (0 : ℝ), ∑' p, f p w by rw [e]; exact H
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  have hw' : 0 < w := hw
  simp only [th]
  rw [tsum_mul_tsum_of_summable_norm (summable_th ha (by positivity)) (summable_th hb hw'),
    ← tsum_div_const]
  refine tsum_congr fun p => ?_
  simp only [hf]
  rw [show v / w * (p.1 : ℝ) = v * p.1 / w by ring]
  ring

/- English proof (translation)
Establish `a0 : a 0 = 0` using `by simpa using ha 0`. Establish `b0 : b 0 = 0` using `by simpa using hb 0`. Establish `H` using `(hasSum_pairs ha hb hv).tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)`. Establish `e : ∀ n : ℕ, ∑' p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n}, a p.val.1 * b p.val.2 * besW (v * p.val.1 * p.val.2) = (∑ p ∈ n.divisorsAntidiagonal, a p.1 * b p.2) * besW (v * n)`. Introduce `n`.

Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Establish `: ∀ p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}, a p.val.1 * b p.val.2 * besW (v * p.val.1 * p.val.2) = 0`. Introduce and unpack `⟨⟨m, n⟩, hp⟩`. Establish `hp' : m * n = 0` using `hp`. Apply the tactic sequence `rcases Nat.mul_eq_zero.1 hp' with rfl | rfl <;> simp [a0, b0]`.

Simplify using `[this]`. Rewrite using `[show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n} = n.divisorsAntidiagonal by ext; simp [hn], Finset.tsum_subtype' n.divisorsAntidiagonal fun p => a p.1 * b p.2 * besW (v * p.1 * p.2), Finset.sum_mul]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite using `[← (Nat.mem_divisorsAntidiagonal.1 hp).1, Nat.cast_mul, mul_assoc v]`. Simplify using `only [e] at H`.

Use `le_hasSum H 1 fun n _ => mul_nonneg (hr n) (besW_nonneg _)` as an intermediate fact. Simplify `this` using `[a1, b1]`.
-/
lemma besW_le_integral {a b : ℕ → ℝ} {D : ℝ} (ha : ∀ n, |a n| ≤ D * n) (hb : ∀ n, |b n| ≤ D * n)
    (a1 : a 1 = 1) (b1 : b 1 = 1)
    (hr : ∀ n : ℕ, 0 ≤ ∑ p ∈ n.divisorsAntidiagonal, a p.1 * b p.2) {v : ℝ} (hv : 0 < v) :
    besW v ≤ ∫ w in Set.Ioi (0 : ℝ), th a (v / w) * th b w / w := by
  have a0 : a 0 = 0 := by simpa using ha 0
  have b0 : b 0 = 0 := by simpa using hb 0
  have H := (hasSum_pairs ha hb hv).tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
  have e : ∀ n : ℕ, ∑' p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n},
      a p.val.1 * b p.val.2 * besW (v * p.val.1 * p.val.2)
      = (∑ p ∈ n.divisorsAntidiagonal, a p.1 * b p.2) * besW (v * n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · have : ∀ p : (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0},
          a p.val.1 * b p.val.2 * besW (v * p.val.1 * p.val.2) = 0 := by
        rintro ⟨⟨m, n⟩, hp⟩
        have hp' : m * n = 0 := hp
        rcases Nat.mul_eq_zero.1 hp' with rfl | rfl <;> simp [a0, b0]
      simp [this]
    · rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {n} = n.divisorsAntidiagonal by ext; simp [hn],
        Finset.tsum_subtype' n.divisorsAntidiagonal
          fun p => a p.1 * b p.2 * besW (v * p.1 * p.2), Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← (Nat.mem_divisorsAntidiagonal.1 hp).1, Nat.cast_mul, mul_assoc v]
  simp only [e] at H
  have := le_hasSum H 1 fun n _ => mul_nonneg (hr n) (besW_nonneg _)
  simpa [a1, b1] using this

def wt (w : ℝ) : ℝ := min w (1 / w) / (Real.sqrt w * w)

/- English proof (translation)
Unfold `wt`. Check the signs of the components of the expression.
-/
lemma wt_nonneg {w : ℝ} (hw : 0 < w) : 0 ≤ wt w := by
  unfold wt; positivity

/- English proof (translation)
Establish `hm : Measurable wt` using `by unfold wt; fun_prop`. Rewrite using `[← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]`. Use `IntegrableOn.union ?_ ?_` and prove the remaining obligations. Use `Integrable.mono' (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2)) (a := 0) (b := 1) (by norm_num)).1 hm.aestronglyMeasurable ?_` and prove the remaining obligations. Use `(ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun w hw => ?_)` and prove the remaining obligations.

Establish `h0 : 0 < w` using `hw.1`. Rewrite using `[Real.norm_of_nonneg (wt_nonneg h0), Real.rpow_neg h0.le, ← Real.sqrt_eq_rpow]`. Establish `hs : 0 < Real.sqrt w` using `Real.sqrt_pos.2 h0`. Unfold `wt`. Combine the equalities or inequalities in the displayed calculation.

Use `Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) one_pos) hm.aestronglyMeasurable ?_` and prove the remaining obligations. Use `(ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)` and prove the remaining obligations. Establish `h1 : 1 < w` using `hw`. Establish `h0 : 0 < w` using `by linarith`. Rewrite using `[Real.norm_of_nonneg (wt_nonneg h0), Real.rpow_neg h0.le, Real.rpow_two]`.

Establish `hs : 1 ≤ Real.sqrt w` using `Real.one_le_sqrt.2 h1.le`. Unfold `wt`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma integrableOn_wt : IntegrableOn wt (Set.Ioi 0) := by
  have hm : Measurable wt := by unfold wt; fun_prop
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2)) (a := 0) (b := 1)
      (by norm_num)).1 hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun w hw => ?_)
    have h0 : 0 < w := hw.1
    rw [Real.norm_of_nonneg (wt_nonneg h0), Real.rpow_neg h0.le, ← Real.sqrt_eq_rpow]
    have hs : 0 < Real.sqrt w := Real.sqrt_pos.2 h0
    unfold wt
    calc min w (1 / w) / (Real.sqrt w * w) ≤ w / (Real.sqrt w * w) := by
          gcongr; exact min_le_left _ _
      _ = _ := by field_simp
  · refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) one_pos)
      hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
    have h1 : 1 < w := hw
    have h0 : 0 < w := by linarith
    rw [Real.norm_of_nonneg (wt_nonneg h0), Real.rpow_neg h0.le, Real.rpow_two]
    have hs : 1 ≤ Real.sqrt w := Real.one_le_sqrt.2 h1.le
    unfold wt
    calc min w (1 / w) / (Real.sqrt w * w) ≤ (1 / w) / (1 * w) := by
          gcongr; exact min_le_right _ _
      _ = _ := by field_simp

/- English proof (translation)
Break down `le_total u 1 with h | h` into its components or cases. Use `(min_le_left _ _).trans (Real.le_sqrt_of_sq_le ?_)` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities. Conclude with `(min_le_right _ _).trans (((div_le_one hu).2 h).trans (Real.one_le_sqrt.2 h))`.
-/
lemma min_le_sqrt {u : ℝ} (hu : 0 < u) : min u (1 / u) ≤ Real.sqrt u := by
  rcases le_total u 1 with h | h
  · refine (min_le_left _ _).trans (Real.le_sqrt_of_sq_le ?_)
    nlinarith
  · exact (min_le_right _ _).trans (((div_le_one hu).2 h).trans (Real.one_le_sqrt.2 h))

/- English proof (translation)
Rewrite using `[← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]`. Use `IntegrableOn.union ?_ ?_` and prove the remaining obligations. Use `Integrable.mono' (g := fun _ => E) (integrableOn_const (by simp)) hm.aestronglyMeasurable ?_` and prove the remaining obligations. Use `(ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun w hw => ?_)` and prove the remaining obligations. Use `(h1 w hw.1).trans ?_` and prove the remaining obligations.

Conclude with `mul_le_of_le_one_right hE ((min_le_left _ _).trans hw.2)`. Use `Integrable.mono' ((exp_neg_integrableOn_Ioi 1 (b := 1 / 2) (by norm_num)).const_mul E') hm.aestronglyMeasurable ?_` and prove the remaining obligations. Use `(ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)` and prove the remaining obligations. Use `(h2 w (le_of_lt hw)).trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma integrableOn_of_bounds {Q : ℝ → ℝ} (hm : Measurable Q) {E E' : ℝ} (hE : 0 ≤ E)
    (h1 : ∀ t, 0 < t → |Q t| ≤ E * min t (1 / t))
    (h2 : ∀ t, 1 ≤ t → |Q t| ≤ E' * Real.exp (-(t / 2))) : IntegrableOn Q (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (g := fun _ => E) (integrableOn_const (by simp)) hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun w hw => ?_)
    refine (h1 w hw.1).trans ?_
    exact mul_le_of_le_one_right hE ((min_le_left _ _).trans hw.2)
  · refine Integrable.mono' ((exp_neg_integrableOn_Ioi 1 (b := 1 / 2) (by norm_num)).const_mul E')
      hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
    refine (h2 w (le_of_lt hw)).trans (le_of_eq ?_)
    congr 2; ring

/- English proof (translation)
Use `set R : ℝ → ℝ := fun w => (P (v / w) - ρ / (v / w)) * Q w / w with hR`. Establish `hRm : Measurable R` using `by simp only [hR]; fun_prop`. Establish `hRb : ∀ w ∈ Set.Ioi (0 : ℝ), |R w| ≤ E ^ 2 * Real.sqrt v * wt w`. Introduce `w hw`. Establish `h0 : 0 < w` using `hw`.

Establish `hs : 0 < Real.sqrt w` using `Real.sqrt_pos.2 h0`. Simplify using `only [hR]`. Rewrite using `[abs_div, abs_mul, abs_of_pos h0]`. Establish `e1 : |P (v / w) - ρ / (v / w)| ≤ E * (Real.sqrt v / Real.sqrt w)`. Use `(h1 _ (by positivity)).trans ?_` and prove the remaining obligations.

Rewrite using `[← Real.sqrt_div hv.le]`. Use `gcongr`. Conclude with `min_le_sqrt (by positivity)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `h2 w h0`.

Use `_ = _ := by unfold wt; field_simp`. Establish `hw` using `integrableOn_wt.const_mul (E ^ 2 * Real.sqrt v)`. Establish `hRi : IntegrableOn R (Set.Ioi 0)` using `Integrable.mono' hw hRm.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hRb))`. Establish `e : ∫ w in Set.Ioi (0 : ℝ), P (v / w) * Q w / w = ∫ w in Set.Ioi (0 : ℝ), (ρ / v * Q w + R w)`. Use `setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_` and prove the remaining obligations.

Establish `h0 : 0 < w` using `hw`. Simplify using `only [hR]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, integral_add (hi.const_mul _) hRi, integral_const_mul, ← integral_const_mul (E ^ 2 * Real.sqrt v)]`.

Use `gcongr ?_ + ?_`. Conclude with `le_rfl`. Conclude with `setIntegral_mono_on hRi hw measurableSet_Ioi fun w hw => (le_abs_self _).trans (hRb w hw)`.
-/
lemma integral_le {P Q : ℝ → ℝ} (hP : Measurable P) (hQ : Measurable Q) {ρ E : ℝ} (hE : 0 ≤ E)
    (h1 : ∀ t, 0 < t → |P t - ρ / t| ≤ E * min t (1 / t))
    (h2 : ∀ t, 0 < t → |Q t| ≤ E * min t (1 / t)) (hi : IntegrableOn Q (Set.Ioi 0))
    {v : ℝ} (hv : 0 < v) :
    ∫ w in Set.Ioi (0 : ℝ), P (v / w) * Q w / w ≤
      ρ / v * (∫ w in Set.Ioi (0 : ℝ), Q w) + E ^ 2 * Real.sqrt v * ∫ w in Set.Ioi (0 : ℝ), wt w := by
  set R : ℝ → ℝ := fun w => (P (v / w) - ρ / (v / w)) * Q w / w with hR
  have hRm : Measurable R := by simp only [hR]; fun_prop
  have hRb : ∀ w ∈ Set.Ioi (0 : ℝ), |R w| ≤ E ^ 2 * Real.sqrt v * wt w := by
    intro w hw
    have h0 : 0 < w := hw
    have hs : 0 < Real.sqrt w := Real.sqrt_pos.2 h0
    simp only [hR]
    rw [abs_div, abs_mul, abs_of_pos h0]
    have e1 : |P (v / w) - ρ / (v / w)| ≤ E * (Real.sqrt v / Real.sqrt w) := by
      refine (h1 _ (by positivity)).trans ?_
      rw [← Real.sqrt_div hv.le]
      gcongr
      exact min_le_sqrt (by positivity)
    calc _ ≤ E * (Real.sqrt v / Real.sqrt w) * (E * min w (1 / w)) / w := by
          gcongr
          exact h2 w h0
      _ = _ := by unfold wt; field_simp
  have hw := integrableOn_wt.const_mul (E ^ 2 * Real.sqrt v)
  have hRi : IntegrableOn R (Set.Ioi 0) :=
    Integrable.mono' hw hRm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hRb))
  have e : ∫ w in Set.Ioi (0 : ℝ), P (v / w) * Q w / w
      = ∫ w in Set.Ioi (0 : ℝ), (ρ / v * Q w + R w) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
    have h0 : 0 < w := hw
    simp only [hR]
    field_simp
    ring
  rw [e, integral_add (hi.const_mul _) hRi, integral_const_mul, ← integral_const_mul (E ^ 2 * Real.sqrt v)]
  gcongr ?_ + ?_
  · exact le_rfl
  · exact setIntegral_mono_on hRi hw measurableSet_Ioi fun w hw => (le_abs_self _).trans (hRb w hw)

def bRe (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ℝ := ∑ g, (χ g).re * 𝓕.a g n

/- English proof (translation)
Establish `: χ g * χ g = 1`. Use `DFunLike.congr_fun h g` as an intermediate fact. Simplify using `using this`. Conclude with `mul_self_eq_one_iff.1 this`.
-/
lemma chi_real {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} (h : χ * χ = 1) (g : 𝓕.G) :
    χ g = 1 ∨ χ g = -1 := by
  have : χ g * χ g = 1 := by
    have := DFunLike.congr_fun h g
    simpa using this
  exact mul_self_eq_one_iff.1 this

/- English proof (translation)
Unfold `LFam.aChi bRe`. Use `push_cast`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases chi_real h g with e | e <;> simp [e]`.
-/
lemma aChi_eq {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} (h : χ * χ = 1) (n : ℕ) :
    𝓕.aChi χ n = (bRe 𝓕 χ n : ℂ) := by
  unfold LFam.aChi bRe
  push_cast
  refine Finset.sum_congr rfl fun g _ => ?_
  rcases chi_real h g with e | e <;> simp [e]

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `[𝓕.a_zero]`. Establish `h1 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `h` using `(abs_le.1 (𝓕.count g n h1)).2`. Rewrite `h` using `[Nat.floor_natCast]`.

Establish `h2 : 𝓕.a g n ≤ ∑ m ∈ Finset.Icc 1 n, 𝓕.a g m` using `Finset.single_le_sum (fun m _ => 𝓕.a_nonneg g m) (Finset.mem_Icc.2 ⟨hn, le_rfl⟩)`. Establish `h3 : Real.sqrt n ≤ n` using `Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩`. Establish `h4 : 𝓕.κ * n ≤ 4 * n` using `mul_le_mul_of_nonneg_right 𝓕.κ_le (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma a_le (𝓕 : LFam) (g : 𝓕.G) (n : ℕ) : 𝓕.a g n ≤ 14 * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [𝓕.a_zero]
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := (abs_le.1 (𝓕.count g n h1)).2
  rw [Nat.floor_natCast] at h
  have h2 : 𝓕.a g n ≤ ∑ m ∈ Finset.Icc 1 n, 𝓕.a g m :=
    Finset.single_le_sum (fun m _ => 𝓕.a_nonneg g m) (Finset.mem_Icc.2 ⟨hn, le_rfl⟩)
  have h3 : Real.sqrt n ≤ n := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have h4 : 𝓕.κ * n ≤ 4 * n := mul_le_mul_of_nonneg_right 𝓕.κ_le (by positivity)
  linarith

/- English proof (translation)
The claim follows from `|bRe 𝓕 χ n| ≤ (Fintype.card 𝓕.G * 14 : ℝ) * n := by unfold bRe refine (Finset.abs_sum_le_sum_abs _ _).trans ?_ refine (Finset.sum_le_card_nsmul _ _ (14 * n : ℝ) fun g _ => ?_).trans (le_of_eq ?_) · rw [abs_mul, abs_of_nonneg (𝓕.a_nonneg g n)] rcases chi_real h g with e | e <;> si …`.
-/
lemma bRe_le {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} (h : χ * χ = 1) (n : ℕ) :
    |bRe 𝓕 χ n| ≤ (Fintype.card 𝓕.G * 14 : ℝ) * n := by
  unfold bRe
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (14 * n : ℝ) fun g _ => ?_).trans (le_of_eq ?_)
  · rw [abs_mul, abs_of_nonneg (𝓕.a_nonneg g n)]
    rcases chi_real h g with e | e <;> simpa [e] using a_le 𝓕 g n
  · simp [mul_assoc]

/- English proof (translation)
Unfold `bRe`. Rewrite using `[Finset.sum_eq_single 0 (fun g _ hg => by simp [𝓕.a_one_ne g hg]) (by simp)]`. Simplify using `[𝓕.a_one]`.
-/
lemma bRe_one (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) : bRe 𝓕 χ 1 = 1 := by
  unfold bRe
  rw [Finset.sum_eq_single 0 (fun g _ hg => by simp [𝓕.a_one_ne g hg]) (by simp)]
  simp [𝓕.a_one]

/- English proof (translation)
Unfold `th`. Rewrite using `[Complex.ofReal_tsum]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[aChi_eq h, Complex.ofReal_mul]`.
-/
lemma th_eq {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} (h : χ * χ = 1) (t : ℝ) :
    ∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) = (th (bRe 𝓕 χ) t : ℂ) := by
  unfold th
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [aChi_eq h, Complex.ofReal_mul]

/- English proof (translation)
Take `⟨C, hC, H⟩` from `GlobalTheory.T.tsum_exp_mul_aChi_bounds`. Use `set K := ∫ w in Set.Ioi (0 : ℝ), wt w with hK`. Establish `hK0 : 0 ≤ K` using `setIntegral_nonneg measurableSet_Ioi fun w hw => wt_nonneg hw`. Establish `hw0` using `besW_one_pos`. Use `set w0 := besW 1 with hw0def`.

Use `set δ := min 1 (w0 / (2 * (C ^ 2 * K + 1))) with hδ`. Establish `hδ0 : 0 < δ` using `by positivity`. Establish `hδ1 : δ ≤ 1` using `min_le_left _ _`. Establish `hδ2 : C ^ 2 * K * δ ≤ w0 / 2`. Establish `h1 : δ ≤ w0 / (2 * (C ^ 2 * K + 1))` using `min_le_right _ _`.

Rewrite `h1` using `[le_div_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨((45 : ℕ) : ℝ), min 1 (δ ^ 2 * w0 / 8), by norm_num, by positivity, fun 𝓕 χ hχ => ?_⟩` and prove the remaining obligations. Rewrite using `[Real.rpow_natCast]`. Establish `hB` using `𝓕.B_ge`.

Establish `hB1 : 1 ≤ 𝓕.B` using `by linarith`. Establish `hB0 : 0 < 𝓕.B` using `by linarith`. Establish `hκ : 0 < 𝓕.κ` using `lt_of_lt_of_le (by positivity) 𝓕.κ_ge`. Establish `hcard : (1 : ℝ) ≤ Fintype.card 𝓕.G` using `by exact_mod_cast Fintype.card_pos`. Distinguish the cases in `h1 : χ = 1`.

Establish `e : 𝓕.F χ 1 = ((𝓕.κ * Fintype.card 𝓕.G : ℝ) : ℂ)`. Simplify using `[LFam.F, LFam.res, h1]`. Rewrite using `[e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `min_le_left _ _`.

Conclude with `le_self_pow₀ hB1 (by norm_num)`. Use `_ ≤ 𝓕.κ := 𝓕.κ_ge`. Use `_ ≤ _ := le_mul_of_one_le_right hκ.le hcard`. Establish `h11 : (1 : AddChar 𝓕.G ℂ) * 1 = 1` using `mul_one _`. Use `set ρ := 𝓕.κ * Fintype.card 𝓕.G with hρ`.

Establish `hP : ∀ t, 0 < t → |th (bRe 𝓕 1) t - ρ / t| ≤ C * 𝓕.B ^ 11 * min t (1 / t)`. Introduce `t ht`. Use `((H 𝓕 1).1 t ht).2` as an intermediate fact. Rewrite `this` using `[th_eq h11, LFam.res, if_pos rfl, ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `this`.

Establish `hQ : ∀ t, 0 < t → |th (bRe 𝓕 χ) t| ≤ C * 𝓕.B ^ 11 * min t (1 / t)`. Introduce `t ht`. Use `((H 𝓕 χ).1 t ht).2` as an intermediate fact. Rewrite `this` using `[th_eq hχ, LFam.res, if_neg h1, zero_div, sub_zero, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `this`.

Establish `hQ' : ∀ t, 1 ≤ t → |th (bRe 𝓕 χ) t| ≤ C * 𝓕.B * Real.exp (-(t / 2))`. Introduce `t ht`. Use `((H 𝓕 χ).2 h1).1 t ht` as an intermediate fact. Rewrite `this` using `[th_eq hχ, Complex.norm_real, Real.norm_eq_abs]`. Conclude with `this`.

Establish `hF : 𝓕.F χ 1 = ((∫ t in Set.Ioi (0 : ℝ), th (bRe 𝓕 χ) t : ℝ) : ℂ)`. Rewrite using `[← ((H 𝓕 χ).2 h1).2]`. Simplify using `only [th_eq hχ]`. Conclude with `integral_ofReal`. Use `set L := ∫ t in Set.Ioi (0 : ℝ), th (bRe 𝓕 χ) t with hL`.

Establish `hE : 0 ≤ C * 𝓕.B ^ 11` using `by positivity`. Use `set s := δ / 𝓕.B ^ 22 with hs`. Establish `hs0 : 0 < s` using `by positivity`. Establish `hs1 : s ≤ 1` using `(div_le_one (by positivity)).2 (hδ1.trans (one_le_pow₀ hB1))`. Establish `hv : 0 < s ^ 2` using `by positivity`.

Establish `hv1 : s ^ 2 ≤ 1` using `pow_le_one₀ hs0.le hs1`. Establish `up` using `integral_le (measurable_th _) (measurable_th _) hE hP hQ (integrableOn_of_bounds (measurable_th _) hE hQ hQ') hv`. Establish `lo` using `besW_le_integral (bRe_le h11) (bRe_le hχ) (bRe_one 𝓕 1) (bRe_one 𝓕 χ) (fun n => by simpa [bRe] using (𝓕.sq χ hχ n).1) hv`. Establish `lo'` using `besW_one_le hv hv1`. Rewrite `up` using `[Real.sqrt_sq hs0.le, ← hL, ← hK]`.

Establish `e1 : (C * 𝓕.B ^ 11) ^ 2 * s * K = C ^ 2 * K * δ`. Rewrite using `[hs]`. Clear the denominators using the available nonvanishing facts. Establish `h2 : w0 / 2 ≤ ρ / s ^ 2 * L` using `by linarith`. Establish `hρ0 : 0 < ρ` using `by positivity`.

Establish `hρ1 : ρ ≤ 4 * 𝓕.B` using `mul_le_mul 𝓕.κ_le 𝓕.card_le (by positivity) (by norm_num)`. Establish `h3 : w0 / 2 ≤ 4 * 𝓕.B / s ^ 2 * |L|` using `h2.trans ((mul_le_mul_of_nonneg_left (le_abs_self L) (by positivity)).trans (by gcongr))`. Rewrite using `[hF, Complex.norm_real, Real.norm_eq_abs]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_F_one_ge : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), χ * χ = 1 →
    c / 𝓕.B ^ A ≤ ‖𝓕.F χ 1‖ := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.T.tsum_exp_mul_aChi_bounds
  set K := ∫ w in Set.Ioi (0 : ℝ), wt w with hK
  have hK0 : 0 ≤ K := setIntegral_nonneg measurableSet_Ioi fun w hw => wt_nonneg hw
  have hw0 := besW_one_pos
  set w0 := besW 1 with hw0def
  set δ := min 1 (w0 / (2 * (C ^ 2 * K + 1))) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : C ^ 2 * K * δ ≤ w0 / 2 := by
    have h1 : δ ≤ w0 / (2 * (C ^ 2 * K + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  refine ⟨((45 : ℕ) : ℝ), min 1 (δ ^ 2 * w0 / 8), by norm_num, by positivity, fun 𝓕 χ hχ => ?_⟩
  rw [Real.rpow_natCast]
  have hB := 𝓕.B_ge
  have hB1 : 1 ≤ 𝓕.B := by linarith
  have hB0 : 0 < 𝓕.B := by linarith
  have hκ : 0 < 𝓕.κ := lt_of_lt_of_le (by positivity) 𝓕.κ_ge
  have hcard : (1 : ℝ) ≤ Fintype.card 𝓕.G := by exact_mod_cast Fintype.card_pos
  by_cases h1 : χ = 1
  · have e : 𝓕.F χ 1 = ((𝓕.κ * Fintype.card 𝓕.G : ℝ) : ℂ) := by
      simp [LFam.F, LFam.res, h1]
    rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc min 1 (δ ^ 2 * w0 / 8) / 𝓕.B ^ 45 ≤ 1 / 𝓕.B := by
          gcongr
          · exact min_le_left _ _
          · exact le_self_pow₀ hB1 (by norm_num)
      _ ≤ 𝓕.κ := 𝓕.κ_ge
      _ ≤ _ := le_mul_of_one_le_right hκ.le hcard
  have h11 : (1 : AddChar 𝓕.G ℂ) * 1 = 1 := mul_one _
  set ρ := 𝓕.κ * Fintype.card 𝓕.G with hρ
  have hP : ∀ t, 0 < t → |th (bRe 𝓕 1) t - ρ / t| ≤ C * 𝓕.B ^ 11 * min t (1 / t) := by
    intro t ht
    have := ((H 𝓕 1).1 t ht).2
    rw [th_eq h11, LFam.res, if_pos rfl, ← Complex.ofReal_div, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hQ : ∀ t, 0 < t → |th (bRe 𝓕 χ) t| ≤ C * 𝓕.B ^ 11 * min t (1 / t) := by
    intro t ht
    have := ((H 𝓕 χ).1 t ht).2
    rw [th_eq hχ, LFam.res, if_neg h1, zero_div, sub_zero,
      Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hQ' : ∀ t, 1 ≤ t → |th (bRe 𝓕 χ) t| ≤ C * 𝓕.B * Real.exp (-(t / 2)) := by
    intro t ht
    have := ((H 𝓕 χ).2 h1).1 t ht
    rw [th_eq hχ, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hF : 𝓕.F χ 1 = ((∫ t in Set.Ioi (0 : ℝ), th (bRe 𝓕 χ) t : ℝ) : ℂ) := by
    rw [← ((H 𝓕 χ).2 h1).2]
    simp only [th_eq hχ]
    exact integral_ofReal
  set L := ∫ t in Set.Ioi (0 : ℝ), th (bRe 𝓕 χ) t with hL
  have hE : 0 ≤ C * 𝓕.B ^ 11 := by positivity
  set s := δ / 𝓕.B ^ 22 with hs
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := (div_le_one (by positivity)).2 (hδ1.trans (one_le_pow₀ hB1))
  have hv : 0 < s ^ 2 := by positivity
  have hv1 : s ^ 2 ≤ 1 := pow_le_one₀ hs0.le hs1
  have up := integral_le (measurable_th _) (measurable_th _) hE hP hQ
    (integrableOn_of_bounds (measurable_th _) hE hQ hQ') hv
  have lo := besW_le_integral (bRe_le h11) (bRe_le hχ) (bRe_one 𝓕 1) (bRe_one 𝓕 χ)
    (fun n => by simpa [bRe] using (𝓕.sq χ hχ n).1) hv
  have lo' := besW_one_le hv hv1
  rw [Real.sqrt_sq hs0.le, ← hL, ← hK] at up
  have e1 : (C * 𝓕.B ^ 11) ^ 2 * s * K = C ^ 2 * K * δ := by
    rw [hs]; field_simp
  have h2 : w0 / 2 ≤ ρ / s ^ 2 * L := by linarith
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 4 * 𝓕.B := mul_le_mul 𝓕.κ_le 𝓕.card_le (by positivity) (by norm_num)
  have h3 : w0 / 2 ≤ 4 * 𝓕.B / s ^ 2 * |L| :=
    h2.trans ((mul_le_mul_of_nonneg_left (le_abs_self L) (by positivity)).trans (by gcongr))
  rw [hF, Complex.norm_real, Real.norm_eq_abs]
  calc min 1 (δ ^ 2 * w0 / 8) / 𝓕.B ^ 45 ≤ (δ ^ 2 * w0 / 8) / 𝓕.B ^ 45 := by
        gcongr; exact min_le_right _ _
    _ = s ^ 2 / (4 * 𝓕.B) * (w0 / 2) := by rw [hs]; field_simp; norm_num
    _ ≤ s ^ 2 / (4 * 𝓕.B) * (4 * 𝓕.B / s ^ 2 * |L|) := by gcongr
    _ = |L| := by field_simp

end GlobalTheory.Hk.RealChar

end
