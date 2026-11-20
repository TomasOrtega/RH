import Mathlib
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

open Finset

namespace Formalism.HermitianLattices.ZeroFreeRegionGL2

/- English proof (translation)
Introduce `K _ _ N α`. Take `⟨r, hr⟩` from `Algebra.norm_one_add_smul (A := ℤ) (B := NumberField.RingOfIntegers K) N α`. Establish `h : (1 + (N : NumberField.RingOfIntegers K) * α) = 1 + N • α`. Rewrite using `[zsmul_eq_mul]`. Rewrite using `[h, hr]`.

Use `(Int.modEq_iff_dvd).2 ⟨-(Algebra.trace ℤ (NumberField.RingOfIntegers K) α + r * N), ?_⟩` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_one_congruence_general : Formalism.HermitianLattices.ZeroFreeRegionGL2.NormOneCongrGeneral := by
  intro K _ _ N α
  obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul (A := ℤ) (B := NumberField.RingOfIntegers K) N α
  have h : (1 + (N : NumberField.RingOfIntegers K) * α) = 1 + N • α := by
    rw [zsmul_eq_mul]
  rw [h, hr]
  refine (Int.modEq_iff_dvd).2 ⟨-(Algebra.trace ℤ (NumberField.RingOfIntegers K) α + r * N), ?_⟩
  ring

/- English proof (translation)
Introduce `ε C' hε hC'`. Use `⟨max 1 ((50 * C' / ε ^ 2) ^ (5 / (2 * ε))), ?_⟩` and prove the remaining obligations. Introduce `x hx NE p hNE hp hlog hpN`. Establish `hx1 : (1 : ℝ) ≤ x` using `le_trans (le_max_left _ _) hx`. Establish `hx0 : (0 : ℝ) < x` using `by linarith`.

Establish `hx2 : (50 * C' / ε ^ 2) ^ (5 / (2 * ε)) ≤ x` using `le_trans (le_max_right _ _) hx`. Establish `hNE0 : (0 : ℝ) < NE` using `by linarith`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `Real.log_le_log hp hpN` as an intermediate fact. Rewrite `this` using `[Real.log_rpow hNE0]`. Then use the resulting hypothesis.

Use `mul_le_mul_of_nonneg_left hlog hC'.le` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `hK : (0 : ℝ) < 50 * C' / ε ^ 2` using `by positivity`. Establish `h1 : Real.log x ≤ x ^ (ε / 5) / (ε / 5)` using `Real.log_le_rpow_div hx0.le (by positivity)`. Establish `hl0 : 0 ≤ Real.log x` using `Real.log_nonneg hx1`.

Establish `h2 : Real.log x ^ 2 ≤ (x ^ (ε / 5) / (ε / 5)) ^ 2` using `pow_le_pow_left₀ hl0 h1 2`. Establish `h3 : 50 * C' / ε ^ 2 ≤ x ^ (2 * ε / 5)`. Use `Real.rpow_le_rpow (by positivity) hx2 (show (0 : ℝ) ≤ 2 * ε / 5 by positivity)` as an intermediate fact. Rewrite `this` using `[← Real.rpow_mul hK.le]`. Establish `e : 5 / (2 * ε) * (2 * ε / 5) = 1` using `by field_simp`.

Rewrite `this` using `[e, Real.rpow_one]`. Then use the resulting hypothesis. Use `set u := x ^ (ε / 5) with hu`. Establish `hu0 : 0 < u` using `Real.rpow_pos_of_pos hx0 _`. Establish `e2 : x ^ (2 * ε / 5) = u ^ 2`. Rewrite using `[hu, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e5 : x ^ ε = u ^ 5`. Rewrite using `[hu, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e5]`. Rewrite `h3` using `[e2]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem log_prime_size_bound : Formalism.HermitianLattices.ZeroFreeRegionGL2.LogPrimeSizeBound := by
  intro ε C' hε hC'
  refine ⟨max 1 ((50 * C' / ε ^ 2) ^ (5 / (2 * ε))), ?_⟩
  intro x hx NE p hNE hp hlog hpN
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hx2 : (50 * C' / ε ^ 2) ^ (5 / (2 * ε)) ≤ x := le_trans (le_max_right _ _) hx
  have hNE0 : (0 : ℝ) < NE := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have := Real.log_le_log hp hpN
    rwa [Real.log_rpow hNE0] at this
  · have := mul_le_mul_of_nonneg_left hlog hC'.le
    calc C' * Real.log NE ≤ C' * (2 * x ^ (ε / 5) * Real.log x ^ 2) := this
      _ = 2 * C' * x ^ (ε / 5) * Real.log x ^ 2 := by ring
  · have hK : (0 : ℝ) < 50 * C' / ε ^ 2 := by positivity
    have h1 : Real.log x ≤ x ^ (ε / 5) / (ε / 5) := Real.log_le_rpow_div hx0.le (by positivity)
    have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h2 : Real.log x ^ 2 ≤ (x ^ (ε / 5) / (ε / 5)) ^ 2 := pow_le_pow_left₀ hl0 h1 2
    have h3 : 50 * C' / ε ^ 2 ≤ x ^ (2 * ε / 5) := by
      have := Real.rpow_le_rpow (by positivity) hx2 (show (0 : ℝ) ≤ 2 * ε / 5 by positivity)
      rw [← Real.rpow_mul hK.le] at this
      have e : 5 / (2 * ε) * (2 * ε / 5) = 1 := by field_simp
      rwa [e, Real.rpow_one] at this
    set u := x ^ (ε / 5) with hu
    have hu0 : 0 < u := Real.rpow_pos_of_pos hx0 _
    have e2 : x ^ (2 * ε / 5) = u ^ 2 := by
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
    have e5 : x ^ ε = u ^ 5 := by
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
    rw [e5]
    rw [e2] at h3
    calc 2 * C' * u * Real.log x ^ 2 ≤ 2 * C' * u * (u / (ε / 5)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (50 * C' / ε ^ 2) * u ^ 3 := by field_simp; ring
      _ ≤ u ^ 2 * u ^ 3 := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = u ^ 5 := by ring

/- English proof (translation)
Rewrite using `[Real.le_log_iff_exp_le (by norm_num)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem one_le_log_twelve : (1 : ℝ) ≤ Real.log 12 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/- English proof (translation)
Introduce `C C₀ c Cρ c₃ hC hC₀ hc hCρ hc₃`. Use `set a : ℝ := Real.log (4 * Cρ) / c with ha`. Use `set t : ℝ := max 1 (max (128 / c₃) (max C₀ (max C (a ^ 2)))) with ht`. Establish `ht1 : 1 ≤ t` using `le_max_left _ _`. Establish `ht2 : 128 / c₃ ≤ t` using `le_trans (le_max_left _ _) (le_max_right _ _)`.

Establish `ht3 : C₀ ≤ t` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)`. Establish `ht4 : C ≤ t` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)`. Establish `ht5 : a ^ 2 ≤ t` using `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)`. Use `clear_value t`. Use `⟨2 * t + 14, by linarith, ?_⟩` and prove the remaining obligations.

Introduce `B hB`. Establish `hB0 : (0 : ℝ) < B` using `by linarith`. Establish `hB1 : (1 : ℝ) ≤ B` using `by linarith`. Establish `hlB : 1 ≤ Real.log B` using `le_trans one_le_log_twelve (Real.log_le_log (by norm_num) hB)`. Establish `hlB0 : 0 < Real.log B` using `by linarith`.

Establish `hlogX : Real.log (B ^ (2 * t + 14)) = (2 * t + 14) * Real.log B` using `Real.log_rpow hB0 _`. Establish `key : ∀ s : ℝ, a ≤ s → Cρ * Real.exp (-c * s) ≤ 1 / 4`. Introduce `s hs`. Establish `h1 : Real.log (4 * Cρ) ≤ c * s`. Use `mul_le_mul_of_nonneg_left hs hc.le` as an intermediate fact.

Rewrite `this` using `[ha]`. Establish `e : c * (Real.log (4 * Cρ) / c) = Real.log (4 * Cρ)` using `by field_simp`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : 4 * Cρ ≤ Real.exp (c * s)`. Rewrite using `[← Real.log_le_iff_le_exp (by positivity)]; exact h1`.

Establish `h3 : Real.exp (-c * s) * Real.exp (c * s) = 1`. Rewrite using `[← Real.exp_add]`. Simplify using the standard rewrite rules. Establish `h4 : 0 < Real.exp (-c * s)` using `Real.exp_pos _`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h2 h4.le]`.

Establish `hat : a ≤ Real.sqrt t` using `Real.le_sqrt_of_sq_le ht5`. Establish `hst : Real.sqrt t ≤ t`. Rewrite using `[Real.sqrt_le_left (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Unfold `Formalism.HermitianLattices.ZeroFreeRegionGL2.rho`. Rewrite using `[hlogX]`. Establish `e1 : -c * ((2 * t + 14) * Real.log B) / Real.log B = -c * (2 * t + 14)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, ← Real.sqrt_eq_rpow]`.

Establish `h1` using `key (2 * t + 14) (by linarith)`. Establish `h2` using `key (Real.sqrt ((2 * t + 14) * Real.log B)) (le_trans hat (Real.sqrt_le_sqrt (by nlinarith)))`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hlogX]`. Establish `hT : (0 : ℝ) < 2 * t + 14` using `by linarith`.

Establish `e1 : (B ^ (2 * t + 14)) ^ (1 / 2 : ℝ) = B ^ (t + 7)`. Rewrite using `[← Real.rpow_mul hB0.le]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : B ^ (-6 : ℝ) * B ^ (2 * t + 14) = B ^ (t + 7) * (B ^ t * B)`.

Rewrite using `[← Real.rpow_add hB0]`. Use `nth_rewrite 4 [← Real.rpow_one B]`. Rewrite using `[← Real.rpow_add hB0, ← Real.rpow_add hB0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hBC : B ^ C ≤ B ^ (t + 7)` using `Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)`. Establish `hP : 0 < B ^ (t + 7)` using `Real.rpow_pos_of_pos hB0 _`. Establish `hlogle : Real.log B ≤ B`. Use `Real.log_le_sub_one_of_pos hB0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hBt : t ^ 2 / 2 ≤ B ^ t`. Establish `h1 : Real.exp t ≤ B ^ t`. Rewrite using `[Real.rpow_def_of_pos hB0]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.

Establish `h2` using `Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ t by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hct : 128 ≤ c₃ * t`. Rewrite `ht2` using `[div_le_iff₀ hc₃]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hmain : 4 * (2 * t + 14) ≤ c₃ * B ^ t`. Establish `h1 : c₃ * (t ^ 2 / 2) ≤ c₃ * B ^ t` using `mul_le_mul_of_nonneg_left hBt hc₃.le`. Establish `h2 : 64 * t ≤ c₃ * (t ^ 2 / 2)` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq : 4 * B ^ (t + 7) ≤ c₃ * B ^ (-6 : ℝ) * B ^ (2 * t + 14) / ((2 * t + 14) * Real.log B)`.

Rewrite using `[le_div_iff₀ (by positivity), mul_assoc c₃, e2]`. Establish `h1 : (2 * t + 14) * Real.log B ≤ (2 * t + 14) * B` using `mul_le_mul_of_nonneg_left hlogle hT.le`. Establish `h2 : 4 * ((2 * t + 14) * B) ≤ c₃ * B ^ t * B`. Use `mul_le_mul_of_nonneg_right hmain hB0.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem choice_of_exponent_constant : Formalism.HermitianLattices.ZeroFreeRegionGL2.ChoiceOfExponentConstant := by
  intro C C₀ c Cρ c₃ hC hC₀ hc hCρ hc₃
  set a : ℝ := Real.log (4 * Cρ) / c with ha
  set t : ℝ := max 1 (max (128 / c₃) (max C₀ (max C (a ^ 2)))) with ht
  have ht1 : 1 ≤ t := le_max_left _ _
  have ht2 : 128 / c₃ ≤ t := le_trans (le_max_left _ _) (le_max_right _ _)
  have ht3 : C₀ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have ht4 : C ≤ t :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have ht5 : a ^ 2 ≤ t :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  clear_value t
  refine ⟨2 * t + 14, by linarith, ?_⟩
  intro B hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hlB : 1 ≤ Real.log B := le_trans one_le_log_twelve (Real.log_le_log (by norm_num) hB)
  have hlB0 : 0 < Real.log B := by linarith
  have hlogX : Real.log (B ^ (2 * t + 14)) = (2 * t + 14) * Real.log B := Real.log_rpow hB0 _

  have key : ∀ s : ℝ, a ≤ s → Cρ * Real.exp (-c * s) ≤ 1 / 4 := by
    intro s hs
    have h1 : Real.log (4 * Cρ) ≤ c * s := by
      have := mul_le_mul_of_nonneg_left hs hc.le
      rw [ha] at this
      have e : c * (Real.log (4 * Cρ) / c) = Real.log (4 * Cρ) := by field_simp
      linarith
    have h2 : 4 * Cρ ≤ Real.exp (c * s) := by
      rw [← Real.log_le_iff_le_exp (by positivity)]; exact h1
    have h3 : Real.exp (-c * s) * Real.exp (c * s) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 : 0 < Real.exp (-c * s) := Real.exp_pos _
    nlinarith [mul_le_mul_of_nonneg_left h2 h4.le]
  have hat : a ≤ Real.sqrt t := Real.le_sqrt_of_sq_le ht5
  have hst : Real.sqrt t ≤ t := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  refine ⟨?_, ?_⟩
  · unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.rho
    rw [hlogX]
    have e1 : -c * ((2 * t + 14) * Real.log B) / Real.log B = -c * (2 * t + 14) := by
      field_simp
    rw [e1, ← Real.sqrt_eq_rpow]
    have h1 := key (2 * t + 14) (by linarith)
    have h2 := key (Real.sqrt ((2 * t + 14) * Real.log B))
      (le_trans hat (Real.sqrt_le_sqrt (by nlinarith)))
    linarith
  · rw [hlogX]

    have hT : (0 : ℝ) < 2 * t + 14 := by linarith
    have e1 : (B ^ (2 * t + 14)) ^ (1 / 2 : ℝ) = B ^ (t + 7) := by
      rw [← Real.rpow_mul hB0.le]; congr 1; ring
    have e2 : B ^ (-6 : ℝ) * B ^ (2 * t + 14) = B ^ (t + 7) * (B ^ t * B) := by
      rw [← Real.rpow_add hB0]
      nth_rewrite 4 [← Real.rpow_one B]
      rw [← Real.rpow_add hB0, ← Real.rpow_add hB0]; congr 1; ring
    have hBC : B ^ C ≤ B ^ (t + 7) := Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
    have hP : 0 < B ^ (t + 7) := Real.rpow_pos_of_pos hB0 _
    have hlogle : Real.log B ≤ B := by
      have := Real.log_le_sub_one_of_pos hB0; linarith

    have hBt : t ^ 2 / 2 ≤ B ^ t := by
      have h1 : Real.exp t ≤ B ^ t := by
        rw [Real.rpow_def_of_pos hB0]
        apply Real.exp_le_exp.2
        nlinarith
      have h2 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ t by linarith)
      linarith
    have hct : 128 ≤ c₃ * t := by
      rw [div_le_iff₀ hc₃] at ht2; linarith
    have hmain : 4 * (2 * t + 14) ≤ c₃ * B ^ t := by
      have h1 : c₃ * (t ^ 2 / 2) ≤ c₃ * B ^ t := mul_le_mul_of_nonneg_left hBt hc₃.le
      have h2 : 64 * t ≤ c₃ * (t ^ 2 / 2) := by nlinarith
      linarith
    have hq : 4 * B ^ (t + 7) ≤ c₃ * B ^ (-6 : ℝ) * B ^ (2 * t + 14) / ((2 * t + 14) * Real.log B) := by
      rw [le_div_iff₀ (by positivity), mul_assoc c₃, e2]
      have h1 : (2 * t + 14) * Real.log B ≤ (2 * t + 14) * B := mul_le_mul_of_nonneg_left hlogle hT.le
      have h2 : 4 * ((2 * t + 14) * B) ≤ c₃ * B ^ t * B := by
        have := mul_le_mul_of_nonneg_right hmain hB0.le
        linarith
      calc 4 * B ^ (t + 7) * ((2 * t + 14) * Real.log B)
          = B ^ (t + 7) * (4 * ((2 * t + 14) * Real.log B)) := by ring
        _ ≤ B ^ (t + 7) * (c₃ * B ^ t * B) := mul_le_mul_of_nonneg_left (by linarith) hP.le
        _ = c₃ * (B ^ (t + 7) * (B ^ t * B)) := by ring
    rw [e1]
    linarith

/- English proof (translation)
Introduce `C₀ c Cρ c₃ hC₀ hc hCρ hc₃ hU C hC`. Take `⟨C₁, hC₁, hN⟩` from `choice_of_exponent_constant C C₀ c Cρ c₃ hC hC₀ hc hCρ hc₃`. Establish `hC₁0 : 0 < C₁` using `lt_of_lt_of_le hC₀ hC₁`. Use `⟨(2 * C + 3) * C₁, by positivity, ?_⟩` and prove the remaining obligations. Introduce `d NE M₀ J hd hd4 hdN hM hMC hJC`.

Establish `hd3 : 3 ≤ d` using `by omega`. Establish `hNE12 : 12 ≤ NE` using `by omega`. Establish `hNEr : (12 : ℝ) ≤ (NE : ℝ)` using `by exact_mod_cast hNE12`. Establish `hNE0 : (0 : ℝ) < (NE : ℝ)` using `by linarith`. Establish `hNE1 : (1 : ℝ) ≤ (NE : ℝ)` using `by linarith`.

Establish `hMr : (1 : ℝ) ≤ (M₀ : ℝ)` using `by exact_mod_cast hM`. Establish `hdr : (3 : ℝ) ≤ (d : ℝ)` using `by exact_mod_cast hd3`. Establish `hdNr : 4 * (d : ℝ) ≤ (NE : ℝ)` using `by exact_mod_cast hdN`. Use `set B : ℝ := 4 * (d : ℝ) * (((M₀ * NE : ℕ) : ℕ) : ℝ) ^ 2 with hBdef`. Establish `hNcast : (((M₀ * NE : ℕ) : ℕ) : ℝ) = (M₀ : ℝ) * (NE : ℝ)` using `by push_cast; ring`.

Establish `hMN : (NE : ℝ) ≤ (M₀ : ℝ) * (NE : ℝ)` using `by nlinarith`. Establish `hBlow : (NE : ℝ) ≤ B`. Rewrite using `[hBdef, hNcast]`. Establish `h1 : (NE : ℝ) ^ 2 ≤ ((M₀ : ℝ) * (NE : ℝ)) ^ 2` using `pow_le_pow_left₀ hNE0.le hMN 2`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hB12 : (12 : ℝ) ≤ B` using `le_trans hNEr hBlow`. Establish `hB0 : (0 : ℝ) < B` using `by linarith`. Establish `hB1 : (1 : ℝ) ≤ B` using `by linarith`. Establish `hBup : B ≤ (NE : ℝ) ^ (2 * C + 3)`. Establish `e : (NE : ℝ) ^ (2 * C + 3) = (NE : ℝ) * (((NE : ℝ) ^ C) * (NE : ℝ)) ^ 2`.

Establish `e1 : (2 * C + 3) = 1 + (C + 1) * (2 : ℕ)` using `by push_cast; ring`. Rewrite using `[e1, Real.rpow_add hNE0, Real.rpow_one, Real.rpow_mul hNE0.le, Real.rpow_natCast, Real.rpow_add hNE0, Real.rpow_one]`. Rewrite using `[e, hBdef, hNcast]`. Establish `h1 : (M₀ : ℝ) * (NE : ℝ) ≤ (NE : ℝ) ^ C * (NE : ℝ)` using `mul_le_mul_of_nonneg_right hMC hNE0.le`. Establish `h2 : ((M₀ : ℝ) * (NE : ℝ)) ^ 2 ≤ ((NE : ℝ) ^ C * (NE : ℝ)) ^ 2` using `pow_le_pow_left₀ (by positivity) h1 2`.

Conclude with `mul_le_mul hdNr h2 (by positivity) hNE0.le`. Take `⟨hrho, hcount⟩` from `hN B hB12`. Establish `hN1 : 1 ≤ M₀ * NE`. Establish `: 1 ≤ NE` using `by omega`. Conclude with `Nat.mul_pos hM this`.

Establish `hU'` using `hU d (M₀ * NE) (B ^ C₁) hd hd4 hN1 (Real.rpow_le_rpow_of_exponent_le hB1 hC₁) hrho`. Establish `hcard : (J : ℝ) ≤ ((Formalism.HermitianLattices.ZeroFreeRegionGL2.normPrimes d (M₀ * NE) 0 (B ^ C₁)).card : ℝ)`. Establish `h1 : (NE : ℝ) ^ C ≤ B ^ C` using `Real.rpow_le_rpow hNE0.le hBlow hC.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcard' : J ≤ (Formalism.HermitianLattices.ZeroFreeRegionGL2.normPrimes d (M₀ * NE) 0 (B ^ C₁)).card` using `by exact_mod_cast hcard`.

Take `⟨S, hS, hSc⟩` from `Finset.exists_subset_card_eq hcard'`. Use `⟨S, hSc, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Establish `hp'` using `hS hp`. Unfold `Formalism.HermitianLattices.ZeroFreeRegionGL2.normPrimes at hp'`.

Simplify using `only [Finset.mem_filter, Finset.mem_Icc] at hp'`. Take `⟨⟨_, hple⟩, hpp, _, hpn⟩` from `hp'`. Use `⟨hpp, hpn, ?_⟩` and prove the remaining obligations. Establish `hX0 : 0 ≤ B ^ C₁` using `(Real.rpow_pos_of_pos hB0 _).le`. Establish `h1 : (p : ℝ) ≤ B ^ C₁` using `le_trans (by exact_mod_cast hple) (Nat.floor_le hX0)`.

Establish `h2 : B ^ C₁ ≤ ((NE : ℝ) ^ (2 * C + 3)) ^ C₁` using `Real.rpow_le_rpow hB0.le hBup hC₁0.le`. Rewrite `h2` using `[← Real.rpow_mul hNE0.le]`. Conclude with `le_trans h1 h2`.
-/
theorem norm_one_estimate_of_hypothesis : Formalism.HermitianLattices.ZeroFreeRegionGL2.PrimeBoundOfUptoHyp := by
  intro C₀ c Cρ c₃ hC₀ hc hCρ hc₃ hU C hC
  obtain ⟨C₁, hC₁, hN⟩ := choice_of_exponent_constant C C₀ c Cρ c₃ hC hC₀ hc hCρ hc₃
  have hC₁0 : 0 < C₁ := lt_of_lt_of_le hC₀ hC₁
  refine ⟨(2 * C + 3) * C₁, by positivity, ?_⟩
  intro d NE M₀ J hd hd4 hdN hM hMC hJC
  have hd3 : 3 ≤ d := by omega
  have hNE12 : 12 ≤ NE := by omega
  have hNEr : (12 : ℝ) ≤ (NE : ℝ) := by exact_mod_cast hNE12
  have hNE0 : (0 : ℝ) < (NE : ℝ) := by linarith
  have hNE1 : (1 : ℝ) ≤ (NE : ℝ) := by linarith
  have hMr : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM
  have hdr : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd3
  have hdNr : 4 * (d : ℝ) ≤ (NE : ℝ) := by exact_mod_cast hdN
  set B : ℝ := 4 * (d : ℝ) * (((M₀ * NE : ℕ) : ℕ) : ℝ) ^ 2 with hBdef
  have hNcast : (((M₀ * NE : ℕ) : ℕ) : ℝ) = (M₀ : ℝ) * (NE : ℝ) := by push_cast; ring
  have hMN : (NE : ℝ) ≤ (M₀ : ℝ) * (NE : ℝ) := by nlinarith
  have hBlow : (NE : ℝ) ≤ B := by
    rw [hBdef, hNcast]
    have h1 : (NE : ℝ) ^ 2 ≤ ((M₀ : ℝ) * (NE : ℝ)) ^ 2 := pow_le_pow_left₀ hNE0.le hMN 2
    nlinarith
  have hB12 : (12 : ℝ) ≤ B := le_trans hNEr hBlow
  have hB0 : (0 : ℝ) < B := by linarith
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hBup : B ≤ (NE : ℝ) ^ (2 * C + 3) := by
    have e : (NE : ℝ) ^ (2 * C + 3) = (NE : ℝ) * (((NE : ℝ) ^ C) * (NE : ℝ)) ^ 2 := by
      have e1 : (2 * C + 3) = 1 + (C + 1) * (2 : ℕ) := by push_cast; ring
      rw [e1, Real.rpow_add hNE0, Real.rpow_one, Real.rpow_mul hNE0.le, Real.rpow_natCast,
        Real.rpow_add hNE0, Real.rpow_one]
    rw [e, hBdef, hNcast]
    have h1 : (M₀ : ℝ) * (NE : ℝ) ≤ (NE : ℝ) ^ C * (NE : ℝ) := mul_le_mul_of_nonneg_right hMC hNE0.le
    have h2 : ((M₀ : ℝ) * (NE : ℝ)) ^ 2 ≤ ((NE : ℝ) ^ C * (NE : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    exact mul_le_mul hdNr h2 (by positivity) hNE0.le
  obtain ⟨hrho, hcount⟩ := hN B hB12
  have hN1 : 1 ≤ M₀ * NE := by
    have : 1 ≤ NE := by omega
    exact Nat.mul_pos hM this
  have hU' := hU d (M₀ * NE) (B ^ C₁) hd hd4 hN1
    (Real.rpow_le_rpow_of_exponent_le hB1 hC₁) hrho
  have hcard : (J : ℝ) ≤ ((Formalism.HermitianLattices.ZeroFreeRegionGL2.normPrimes d (M₀ * NE) 0 (B ^ C₁)).card : ℝ) := by
    have h1 : (NE : ℝ) ^ C ≤ B ^ C := Real.rpow_le_rpow hNE0.le hBlow hC.le
    linarith
  have hcard' : J ≤ (Formalism.HermitianLattices.ZeroFreeRegionGL2.normPrimes d (M₀ * NE) 0 (B ^ C₁)).card := by exact_mod_cast hcard
  obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq hcard'
  refine ⟨S, hSc, ?_⟩
  intro p hp
  have hp' := hS hp
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.normPrimes at hp'
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp'
  obtain ⟨⟨_, hple⟩, hpp, _, hpn⟩ := hp'
  refine ⟨hpp, hpn, ?_⟩
  have hX0 : 0 ≤ B ^ C₁ := (Real.rpow_pos_of_pos hB0 _).le
  have h1 : (p : ℝ) ≤ B ^ C₁ := le_trans (by exact_mod_cast hple) (Nat.floor_le hX0)
  have h2 : B ^ C₁ ≤ ((NE : ℝ) ^ (2 * C + 3)) ^ C₁ := Real.rpow_le_rpow hB0.le hBup hC₁0.le
  rw [← Real.rpow_mul hNE0.le] at h2
  exact le_trans h1 h2

end Formalism.HermitianLattices.ZeroFreeRegionGL2
