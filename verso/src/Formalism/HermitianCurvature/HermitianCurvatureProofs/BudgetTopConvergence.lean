import Formalism.HermitianCurvature.StatementU

open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace Formalism.FourierDecayAlt.P.Ux7

/- English proof (translation)
Introduce `N j r hj hjr`. Use `⟨Nat.mul_le_mul_left N hjr, ?_⟩` and prove the remaining obligations. Establish `h1 : j ≤ r ^ 2` using `hjr.trans (Nat.le_self_pow (by norm_num) r)`. Establish `h2 : j ^ 2 ≤ r ^ 2` using `Nat.pow_le_pow_left hjr 2`. Establish `a` using `Nat.mul_le_mul_left N h1`.

Establish `b` using `Nat.mul_le_mul_left N h2`. Establish `c : j * (N * j) = N * j ^ 2` using `by ring`. Rewrite using `[c]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem budgetWord : BudgetWord := by
  intro N j r hj hjr
  refine ⟨Nat.mul_le_mul_left N hjr, ?_⟩
  have h1 : j ≤ r ^ 2 := hjr.trans (Nat.le_self_pow (by norm_num) r)
  have h2 : j ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hjr 2
  have a := Nat.mul_le_mul_left N h1
  have b := Nat.mul_le_mul_left N h2
  have c : j * (N * j) = N * j ^ 2 := by ring
  rw [c]
  nlinarith

/- English proof (translation)
Introduce `N r n h`. Establish `h1 : 3 * r ^ 2 ≤ n ^ 2` using `by nlinarith`. Establish `h2` using `Nat.mul_le_mul_left N h1`. Use polynomial arithmetic with `[Nat.zero_le (n ^ 3)]`.
-/
theorem budgetWordStar : BudgetWordStar := by
  intro N r n h
  have h1 : 3 * r ^ 2 ≤ n ^ 2 := by nlinarith
  have h2 := Nat.mul_le_mul_left N h1
  nlinarith [Nat.zero_le (n ^ 3)]

/- English proof (translation)
Introduce `x A hx hA`. Use `le_min ?_ ?_` and prove the remaining obligations. Conclude with `Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)`. Rewrite using `[Real.rpow_neg (by linarith), Real.rpow_neg hx.le]`. Establish `h1 : 0 < x ^ A` using `Real.rpow_pos_of_pos hx A`.

Establish `h2 : x ^ A ≤ (1 + x) ^ A` using `Real.rpow_le_rpow hx.le (by linarith) hA`. Use `first`. Consider the case `exact inv_anti₀ h1 h2`. Consider the case `exact inv_le_inv_of_le h1 h2`.
-/
theorem decayMin : DecayMin := by
  intro x A hx hA
  refine le_min ?_ ?_
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  · rw [Real.rpow_neg (by linarith), Real.rpow_neg hx.le]
    have h1 : 0 < x ^ A := Real.rpow_pos_of_pos hx A
    have h2 : x ^ A ≤ (1 + x) ^ A := Real.rpow_le_rpow hx.le (by linarith) hA
    first
      | exact inv_anti₀ h1 h2
      | exact inv_le_inv_of_le h1 h2

/- English proof (translation)
Establish `e1 : ∀ x : ℂ, (cStd * (starRingEnd ℂ) x).re = (betaU * x).re`. Introduce `x`. Simplify using `[cStd, betaU, Complex.mul_re]`. Establish `e2 : ∀ x : ℂ, (betaU * x).re = -(cStd * x).re`. Introduce `x`.

Simplify using `[cStd, betaU, Complex.mul_re]`. Use `⟨?_, ?_, fun x => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Apply the tactic sequence `apply Complex.ext <;> simp [cStd, betaU]`. Simplify using `[betaU, cStd]`. Simplify using `only [G.psi]`.

Rewrite using `[e1]`. Simplify using `only [G.psi]`. Rewrite using `[e2]`. Use `show (starRingEnd ℂ) (Complex.exp _) = _`. Rewrite using `[← Complex.exp_conj]`.

Use `congr 1`. Rewrite using `[map_mul, Complex.conj_I, Complex.conj_ofReal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem scaleMatch : ScaleMatch := by
  have e1 : ∀ x : ℂ, (cStd * (starRingEnd ℂ) x).re = (betaU * x).re := by
    intro x
    simp [cStd, betaU, Complex.mul_re]
  have e2 : ∀ x : ℂ, (betaU * x).re = -(cStd * x).re := by
    intro x
    simp [cStd, betaU, Complex.mul_re]
  refine ⟨?_, ?_, fun x => ⟨?_, ?_⟩⟩
  · apply Complex.ext <;> simp [cStd, betaU]
  · simp [betaU, cStd]
  · simp only [G.psi]
    rw [e1]
  · simp only [G.psi]
    rw [e2]
    show (starRingEnd ℂ) (Complex.exp _) = _
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring

/- English proof (translation)
Introduce `r m mmB o κjo As Cc A₀ hr hm hmm ho hk hCc hA`. Establish `hX : (m + 1 + mmB) + o ≤ 3 * As` using `by omega`. Use `⟨hX, ?_⟩` and prove the remaining obligations. Establish `hrR : (1 : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hXR : ((((m + 1 + mmB) + o : ℕ)) : ℝ) ≤ 3 * As` using `by exact_mod_cast hX`.

Establish `hkR : (κjo : ℝ) ≤ As` using `by exact_mod_cast hk`. Establish `hmR : (m : ℝ) + 1 ≤ As` using `by exact_mod_cast hm`. Establish `hmmR : (mmB : ℝ) ≤ As` using `by exact_mod_cast hmm`. Establish `hAs0 : (0 : ℝ) ≤ As` using `Nat.cast_nonneg _`. Establish `hr0 : (0 : ℝ) ≤ r` using `by linarith`.

Establish `p1` using `mul_le_mul_of_nonneg_left hXR (show (0 : ℝ) ≤ 2 * ((r : ℝ) + 1) by linarith)`. Establish `p2` using `mul_le_mul_of_nonneg_left hmR (show (0 : ℝ) ≤ 5 * (r : ℝ) by linarith)`. Establish `p3` using `mul_le_mul_of_nonneg_left hmmR (show (0 : ℝ) ≤ 2 * (r : ℝ) by linarith)`. Establish `h2 : A₀ - (As : ℝ) - 6 * ((r : ℝ) + 1) * (As : ℝ) ≤ A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * ((((m + 1 + mmB) + o : ℕ)) : ℝ)` using `by nlinarith`. Establish `h3' : A₀ - (13 * (r : ℝ) + 7) * (As : ℝ) ≤ A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * ((((m + 1 + mmB) + o : ℕ)) : ℝ) - 5 * r * ((m : ℝ) + 1) - 2 * r * mmB` using `by nlinarith`.

Establish `hden : (0 : ℝ) < 8 * (2 * (r : ℝ) + 1)` using `by linarith`. Establish `ha1 : 8 * (2 * (r : ℝ) + 1) * a1 r (A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * ((((m + 1 + mmB) + o : ℕ)) : ℝ)) m mmB = A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * ((((m + 1 + mmB) + o : ℕ)) : ℝ) - 5 * r * ((m : ℝ) + 1) - 2 * r * mmB`. Unfold `a1`. Clear the denominators using the available nonvanishing facts. Establish `hrA : (0 : ℝ) ≤ r * As` using `mul_nonneg hr0 hAs0`.

Use `⟨h2, by rw [ha1]; exact h3', by nlinarith, ?_⟩` and prove the remaining obligations. Apply `le_of_mul_le_mul_left _ hden` to reduce the goal to its premises. Rewrite using `[ha1]`. Establish `hQ : 0 ≤ (Cc - 20) * (((r : ℝ) + 1) ^ 3 * As)` using `mul_nonneg (by linarith) (by positivity)`. Establish `h4 : 1 + 4 * (r : ℝ) ≤ ((r : ℝ) + 1) ^ 4`.

Use polynomial arithmetic with `[pow_nonneg hr0 2, pow_nonneg hr0 3, pow_nonneg hr0 4]`. Establish `h5` using `mul_le_mul_of_nonneg_right h4 hAs0`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem budget_second_corollary_holds : DerivativeBudgetCount := by
  intro r m mmB o κjo As Cc A₀ hr hm hmm ho hk hCc hA
  have hX : (m + 1 + mmB) + o ≤ 3 * As := by omega
  refine ⟨hX, ?_⟩
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hXR : ((((m + 1 + mmB) + o : ℕ)) : ℝ) ≤ 3 * As := by exact_mod_cast hX
  have hkR : (κjo : ℝ) ≤ As := by exact_mod_cast hk
  have hmR : (m : ℝ) + 1 ≤ As := by exact_mod_cast hm
  have hmmR : (mmB : ℝ) ≤ As := by exact_mod_cast hmm
  have hAs0 : (0 : ℝ) ≤ As := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have p1 := mul_le_mul_of_nonneg_left hXR (show (0 : ℝ) ≤ 2 * ((r : ℝ) + 1) by linarith)
  have p2 := mul_le_mul_of_nonneg_left hmR (show (0 : ℝ) ≤ 5 * (r : ℝ) by linarith)
  have p3 := mul_le_mul_of_nonneg_left hmmR (show (0 : ℝ) ≤ 2 * (r : ℝ) by linarith)
  have h2 : A₀ - (As : ℝ) - 6 * ((r : ℝ) + 1) * (As : ℝ) ≤
      A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * ((((m + 1 + mmB) + o : ℕ)) : ℝ) := by nlinarith
  have h3' : A₀ - (13 * (r : ℝ) + 7) * (As : ℝ) ≤
      A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * ((((m + 1 + mmB) + o : ℕ)) : ℝ) - 5 * r * ((m : ℝ) + 1) -
        2 * r * mmB := by nlinarith
  have hden : (0 : ℝ) < 8 * (2 * (r : ℝ) + 1) := by linarith
  have ha1 : 8 * (2 * (r : ℝ) + 1) *
      a1 r (A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * ((((m + 1 + mmB) + o : ℕ)) : ℝ)) m mmB =
      A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * ((((m + 1 + mmB) + o : ℕ)) : ℝ) - 5 * r * ((m : ℝ) + 1) -
        2 * r * mmB := by
    unfold a1
    field_simp
  have hrA : (0 : ℝ) ≤ r * As := mul_nonneg hr0 hAs0
  refine ⟨h2, by rw [ha1]; exact h3', by nlinarith, ?_⟩
  apply le_of_mul_le_mul_left _ hden
  rw [ha1]
  have hQ : 0 ≤ (Cc - 20) * (((r : ℝ) + 1) ^ 3 * As) :=
    mul_nonneg (by linarith) (by positivity)
  have h4 : 1 + 4 * (r : ℝ) ≤ ((r : ℝ) + 1) ^ 4 := by
    nlinarith [pow_nonneg hr0 2, pow_nonneg hr0 3, pow_nonneg hr0 4]
  have h5 := mul_le_mul_of_nonneg_right h4 hAs0
  calc 8 * (2 * (r : ℝ) + 1) * ((Cc - 20) / 16 * ((r : ℝ) + 1) ^ 3 * (As : ℝ))
      = (2 * (r : ℝ) + 1) / 2 * ((Cc - 20) * (((r : ℝ) + 1) ^ 3 * As)) := by ring
    _ ≤ ((r : ℝ) + 1) * ((Cc - 20) * (((r : ℝ) + 1) ^ 3 * As)) :=
        mul_le_mul_of_nonneg_right (by linarith) hQ
    _ = Cc * (((r : ℝ) + 1) ^ 4 * As) - 20 * (((r : ℝ) + 1) ^ 4 * As) := by ring
    _ ≤ Cc * (((r : ℝ) + 1) ^ 4 * As) - (13 * (r : ℝ) + 7) * As := by nlinarith
    _ ≤ A₀ - (13 * (r : ℝ) + 7) * (As : ℝ) := by nlinarith
    _ ≤ _ := h3'

/- English proof (translation)
Introduce `r n s As C₁ c AB hn hs hAs hAB hc hC`. Establish `hnR : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hAsR : (n : ℝ) ^ 3 ≤ As` using `by exact_mod_cast hAs`. Establish `hsR : (s : ℝ) ≤ r` using `by exact_mod_cast hs`. Establish `hr0 : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`.

Establish `hs0 : (0 : ℝ) ≤ s` using `Nat.cast_nonneg s`. Establish `hn3 : (n : ℝ) ≤ (n : ℝ) ^ 3`. Simplify using `using pow_le_pow_right₀ hnR (show 1 ≤ 3 by norm_num)`. Establish `hAs1 : (1 : ℝ) ≤ As` using `by nlinarith`. Establish `hnA : (n : ℝ) ≤ As` using `by linarith`.

Establish `hR : (1 : ℝ) + 3 * r ≤ ((r : ℝ) + 1) ^ 3` using `by nlinarith [sq_nonneg (r : ℝ)]`. Establish `hP : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3` using `by linarith`. Establish `hPA : 0 ≤ ((r : ℝ) + 1) ^ 3 * (As : ℝ)` using `by positivity`. Establish `key : ((r : ℝ) + 1) ^ 3 * (As : ℝ) ≤ c * ((r : ℝ) + 1) ^ 3 * (As : ℝ)`. Use the polynomial consequences of the given equalities and inequalities.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e1 : 2 * (r : ℝ) * n ≤ 2 * r * As` using `by nlinarith`. Establish `e2 : 2 * (r : ℝ) * As < (1 + 3 * r) * As` using `by nlinarith`. Establish `e3 : (1 + 3 * (r : ℝ)) * As ≤ ((r : ℝ) + 1) ^ 3 * As` using `mul_le_mul_of_nonneg_right hR (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e3 : (As : ℝ) ≤ ((r : ℝ) + 1) ^ 3 * As` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e1 : (s : ℝ) ^ 2 ≤ ((r : ℝ) + 1) ^ 3` using `by nlinarith [mul_le_mul hsR hsR hs0 hr0]`. Establish `hC0 : (0 : ℝ) ≤ C₁` using `Nat.cast_nonneg _`. Establish `e2 : (C₁ : ℝ) * s ^ 2 ≤ c * ((r : ℝ) + 1) ^ 3`.

Combine the equalities or inequalities in the displayed calculation. Establish `hcP : 0 ≤ c * ((r : ℝ) + 1) ^ 3` using `mul_nonneg (by linarith) (by positivity)`. Establish `e3 : c * ((r : ℝ) + 1) ^ 3 ≤ c * ((r : ℝ) + 1) ^ 3 * As` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem thresholds_second_corollary_holds : GermThresholds := by
  intro r n s As C₁ c AB hn hs hAs hAB hc hC
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hAsR : (n : ℝ) ^ 3 ≤ As := by exact_mod_cast hAs
  have hsR : (s : ℝ) ≤ r := by exact_mod_cast hs
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hn3 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    simpa using pow_le_pow_right₀ hnR (show 1 ≤ 3 by norm_num)
  have hAs1 : (1 : ℝ) ≤ As := by nlinarith
  have hnA : (n : ℝ) ≤ As := by linarith
  have hR : (1 : ℝ) + 3 * r ≤ ((r : ℝ) + 1) ^ 3 := by nlinarith [sq_nonneg (r : ℝ)]
  have hP : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := by linarith
  have hPA : 0 ≤ ((r : ℝ) + 1) ^ 3 * (As : ℝ) := by positivity
  have key : ((r : ℝ) + 1) ^ 3 * (As : ℝ) ≤ c * ((r : ℝ) + 1) ^ 3 * (As : ℝ) := by
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have e1 : 2 * (r : ℝ) * n ≤ 2 * r * As := by nlinarith
    have e2 : 2 * (r : ℝ) * As < (1 + 3 * r) * As := by nlinarith
    have e3 : (1 + 3 * (r : ℝ)) * As ≤ ((r : ℝ) + 1) ^ 3 * As :=
      mul_le_mul_of_nonneg_right hR (by linarith)
    linarith
  · have e3 : (As : ℝ) ≤ ((r : ℝ) + 1) ^ 3 * As := by nlinarith
    linarith
  · have e1 : (s : ℝ) ^ 2 ≤ ((r : ℝ) + 1) ^ 3 := by nlinarith [mul_le_mul hsR hsR hs0 hr0]
    have hC0 : (0 : ℝ) ≤ C₁ := Nat.cast_nonneg _
    have e2 : (C₁ : ℝ) * s ^ 2 ≤ c * ((r : ℝ) + 1) ^ 3 :=
      calc (C₁ : ℝ) * s ^ 2 ≤ c * s ^ 2 := mul_le_mul_of_nonneg_right hC (by positivity)
        _ ≤ c * ((r : ℝ) + 1) ^ 3 := mul_le_mul_of_nonneg_left e1 (by linarith)
    have hcP : 0 ≤ c * ((r : ℝ) + 1) ^ 3 := mul_nonneg (by linarith) (by positivity)
    have e3 : c * ((r : ℝ) + 1) ^ 3 ≤ c * ((r : ℝ) + 1) ^ 3 * As := by nlinarith
    linarith

/- English proof (translation)
Introduce `m M β t D V _ _ Φ hM ht`. Take `⟨M', rfl⟩ : ∃ M', M = M' + 2` from `⟨M - 2, by omega⟩`. Establish `hnt : ‖t‖ ≠ 0` using `norm_ne_zero_iff.mpr ht`. Establish `key : ((‖t‖ ^ (m + 1))⁻¹ * ‖t‖ ^ ((m + 1) * (M' + 2 + m)) * ‖D / t ^ (m + 1)‖ ^ M' : ℝ) = ‖D‖ ^ M' * ‖t‖ ^ ((m + 1) ^ 2)`. Rewrite using `[norm_div, norm_pow, div_pow]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hc : D / t ^ (m + 1) * t ^ (m + 1) = D` using `div_mul_cancel₀ D (pow_ne_zero _ ht)`. Simplify using `only [uD, aD, G.remainder, Nat.add_sub_cancel]`. Rewrite using `[key, hc, smul_sub, smul_smul, Complex.ofReal_mul]`.
-/
theorem powerMatch : PowerMatch := by
  intro m M β t D V _ _ Φ hM ht
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 2 := ⟨M - 2, by omega⟩
  have hnt : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  have key : ((‖t‖ ^ (m + 1))⁻¹ * ‖t‖ ^ ((m + 1) * (M' + 2 + m)) * ‖D / t ^ (m + 1)‖ ^ M' : ℝ) =
      ‖D‖ ^ M' * ‖t‖ ^ ((m + 1) ^ 2) := by
    rw [norm_div, norm_pow, div_pow]
    field_simp
    ring
  have hc : D / t ^ (m + 1) * t ^ (m + 1) = D := div_mul_cancel₀ D (pow_ne_zero _ ht)
  simp only [uD, aD, G.remainder, Nat.add_sub_cancel]
  rw [key, hc, smul_sub, smul_smul, Complex.ofReal_mul]

/- English proof (translation)
Introduce `C₁ C₂ Ca`. Use `⟨5 * (C₁ : ℝ) + 9 * Ca + Ca * C₂ + 1, ?_⟩` and prove the remaining obligations. Introduce `r n s As al A A₀ hn hs hAs hal hA₀ hA`. Use `set X : ℝ := (r : ℝ) + 1 with hXdef`. Establish `hr0 : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`.

Establish `hX1 : (1 : ℝ) ≤ X` using `by linarith`. Establish `hX0 : (0 : ℝ) ≤ X` using `by linarith`. Establish `hsX : (s : ℝ) ≤ X`. Establish `: (s : ℝ) ≤ (r : ℝ) + 1` using `by exact_mod_cast hs`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hrX : (r : ℝ) ≤ X` using `by linarith`. Establish `hn1 : (1 : ℝ) ≤ n`. Establish `: 1 ≤ n` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hAsR : (n : ℝ) ^ 3 ≤ As` using `by exact_mod_cast hAs`.

Establish `hn2 : (n : ℝ) ^ 2 ≤ As` using `(pow_le_pow_right₀ hn1 (show 2 ≤ 3 by norm_num)).trans hAsR`. Establish `hW1 : (1 : ℝ) ≤ As` using `(one_le_pow₀ hn1).trans hAsR`. Establish `halR : (al : ℝ) ≤ C₂ * (s : ℝ) ^ 2 + 1` using `by exact_mod_cast hal`. Establish `hC₁ : (0 : ℝ) ≤ C₁` using `Nat.cast_nonneg _`. Establish `hCa : (0 : ℝ) ≤ Ca` using `Nat.cast_nonneg _`.

Establish `hC₂ : (0 : ℝ) ≤ C₂` using `Nat.cast_nonneg _`. Establish `hs0 : (0 : ℝ) ≤ s` using `Nat.cast_nonneg _`. Establish `hal0 : (0 : ℝ) ≤ al` using `Nat.cast_nonneg _`. Establish `hX4p : (1 : ℝ) ≤ X ^ 4` using `one_le_pow₀ hX1`. Establish `hT1 : (1 : ℝ) ≤ X ^ 4 * As` using `one_le_mul_of_one_le_of_one_le hX4p hW1`.

Establish `hX3 : X ^ 3 ≤ X ^ 4` using `pow_le_pow_right₀ hX1 (by norm_num)`. Establish `hX2 : X ^ 2 ≤ X ^ 4` using `pow_le_pow_right₀ hX1 (by norm_num)`. Establish `hXX : X ≤ X ^ 4` using `by simpa using pow_le_pow_right₀ hX1 (show 1 ≤ 4 by norm_num)`. Establish `hX4 : X ^ 4 ≤ X ^ 4 * As` using `le_mul_of_one_le_right (by positivity) hW1`. Establish `hX3T : X ^ 3 ≤ X ^ 4 * As` using `hX3.trans hX4`.

Establish `hWT : (As : ℝ) ≤ X ^ 4 * As` using `le_mul_of_one_le_left (by linarith) hX4p`. Establish `hXW : X * As ≤ X ^ 4 * As` using `mul_le_mul_of_nonneg_right hXX (by linarith)`. Establish `b2 : (Ca : ℝ) * r ^ 2 * (5 * X) ≤ 5 * Ca * (X ^ 4 * As)`. Establish `c : (r : ℝ) ^ 2 * X ≤ X ^ 3`. Combine the equalities or inequalities in the displayed calculation.

Establish `c'` using `mul_le_mul_of_nonneg_left (c.trans hX3T) (show (0 : ℝ) ≤ 5 * Ca by linarith)`. Combine the equalities or inequalities in the displayed calculation. Establish `b3 : (Ca : ℝ) * ((n : ℝ) ^ 2 + (r : ℝ) ^ 3 + (r : ℝ) * (al : ℝ)) ≤ (Ca * (3 + C₂)) * (X ^ 4 * As)`. Establish `c1 : (r : ℝ) ^ 3 ≤ X ^ 3` using `by gcongr`. Establish `hss : (s : ℝ) ^ 2 ≤ X ^ 2` using `by gcongr`.

Establish `c2a : (al : ℝ) ≤ C₂ * X ^ 2 + 1` using `by linarith [mul_le_mul_of_nonneg_left hss hC₂]`. Establish `c2 : (r : ℝ) * al ≤ X * (C₂ * X ^ 2 + 1)` using `mul_le_mul hrX c2a hal0 hX0`. Establish `c3 : X * (C₂ * X ^ 2 + 1) = C₂ * X ^ 3 + X` using `by ring`. Establish `c4` using `mul_le_mul_of_nonneg_left hX3T hC₂`. Establish `c5 : X ≤ X ^ 4 * As` using `hXX.trans hX4`.

Establish `: (n : ℝ) ^ 2 + (r : ℝ) ^ 3 + (r : ℝ) * (al : ℝ) ≤ (3 + C₂) * (X ^ 4 * As)`. Rewrite `c2` using `[c3]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `b4 : (Ca : ℝ) * r * As ≤ Ca * (X ^ 4 * As)`.

Use `mul_le_mul_of_nonneg_right hrX (show (0 : ℝ) ≤ As by linarith)` as an intermediate fact. Use `mul_le_mul_of_nonneg_left (this.trans hXW) hCa` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `b1 : (C₁ : ℝ) * s ^ 3 * (5 * X) ≤ 5 * C₁ * (X ^ 4 * As)`. Establish `c : (s : ℝ) ^ 3 * X ≤ X ^ 4`.

Combine the equalities or inequalities in the displayed calculation. Establish `c'` using `mul_le_mul_of_nonneg_left (c.trans hX4) (show (0 : ℝ) ≤ 5 * C₁ by linarith)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[le_sub_iff_add_le, le_div_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem budgetTop : BudgetTop := by
  intro C₁ C₂ Ca
  refine ⟨5 * (C₁ : ℝ) + 9 * Ca + Ca * C₂ + 1, ?_⟩
  intro r n s As al A A₀ hn hs hAs hal hA₀ hA
  set X : ℝ := (r : ℝ) + 1 with hXdef
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hsX : (s : ℝ) ≤ X := by
    have : (s : ℝ) ≤ (r : ℝ) + 1 := by exact_mod_cast hs
    linarith
  have hrX : (r : ℝ) ≤ X := by linarith
  have hn1 : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hAsR : (n : ℝ) ^ 3 ≤ As := by exact_mod_cast hAs
  have hn2 : (n : ℝ) ^ 2 ≤ As := (pow_le_pow_right₀ hn1 (show 2 ≤ 3 by norm_num)).trans hAsR
  have hW1 : (1 : ℝ) ≤ As := (one_le_pow₀ hn1).trans hAsR
  have halR : (al : ℝ) ≤ C₂ * (s : ℝ) ^ 2 + 1 := by exact_mod_cast hal
  have hC₁ : (0 : ℝ) ≤ C₁ := Nat.cast_nonneg _
  have hCa : (0 : ℝ) ≤ Ca := Nat.cast_nonneg _
  have hC₂ : (0 : ℝ) ≤ C₂ := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hal0 : (0 : ℝ) ≤ al := Nat.cast_nonneg _
  have hX4p : (1 : ℝ) ≤ X ^ 4 := one_le_pow₀ hX1
  have hT1 : (1 : ℝ) ≤ X ^ 4 * As := one_le_mul_of_one_le_of_one_le hX4p hW1
  have hX3 : X ^ 3 ≤ X ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
  have hX2 : X ^ 2 ≤ X ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
  have hXX : X ≤ X ^ 4 := by simpa using pow_le_pow_right₀ hX1 (show 1 ≤ 4 by norm_num)
  have hX4 : X ^ 4 ≤ X ^ 4 * As := le_mul_of_one_le_right (by positivity) hW1
  have hX3T : X ^ 3 ≤ X ^ 4 * As := hX3.trans hX4
  have hWT : (As : ℝ) ≤ X ^ 4 * As := le_mul_of_one_le_left (by linarith) hX4p
  have hXW : X * As ≤ X ^ 4 * As := mul_le_mul_of_nonneg_right hXX (by linarith)
  have b2 : (Ca : ℝ) * r ^ 2 * (5 * X) ≤ 5 * Ca * (X ^ 4 * As) := by
    have c : (r : ℝ) ^ 2 * X ≤ X ^ 3 :=
      calc (r : ℝ) ^ 2 * X ≤ X ^ 2 * X := by gcongr
        _ = X ^ 3 := by ring
    have c' := mul_le_mul_of_nonneg_left (c.trans hX3T) (show (0 : ℝ) ≤ 5 * Ca by linarith)
    calc (Ca : ℝ) * r ^ 2 * (5 * X) = 5 * Ca * ((r : ℝ) ^ 2 * X) := by ring
      _ ≤ _ := c'
  have b3 : (Ca : ℝ) * ((n : ℝ) ^ 2 + (r : ℝ) ^ 3 + (r : ℝ) * (al : ℝ)) ≤ (Ca * (3 + C₂)) * (X ^ 4 * As) := by
    have c1 : (r : ℝ) ^ 3 ≤ X ^ 3 := by gcongr
    have hss : (s : ℝ) ^ 2 ≤ X ^ 2 := by gcongr
    have c2a : (al : ℝ) ≤ C₂ * X ^ 2 + 1 := by linarith [mul_le_mul_of_nonneg_left hss hC₂]
    have c2 : (r : ℝ) * al ≤ X * (C₂ * X ^ 2 + 1) := mul_le_mul hrX c2a hal0 hX0
    have c3 : X * (C₂ * X ^ 2 + 1) = C₂ * X ^ 3 + X := by ring
    have c4 := mul_le_mul_of_nonneg_left hX3T hC₂
    have c5 : X ≤ X ^ 4 * As := hXX.trans hX4
    have : (n : ℝ) ^ 2 + (r : ℝ) ^ 3 + (r : ℝ) * (al : ℝ) ≤ (3 + C₂) * (X ^ 4 * As) := by
      rw [c3] at c2
      linarith
    calc (Ca : ℝ) * ((n : ℝ) ^ 2 + (r : ℝ) ^ 3 + (r : ℝ) * (al : ℝ))
        ≤ Ca * ((3 + C₂) * (X ^ 4 * As)) := mul_le_mul_of_nonneg_left this hCa
      _ = _ := by ring
  have b4 : (Ca : ℝ) * r * As ≤ Ca * (X ^ 4 * As) := by
    have := mul_le_mul_of_nonneg_right hrX (show (0 : ℝ) ≤ As by linarith)
    have := mul_le_mul_of_nonneg_left (this.trans hXW) hCa
    linarith
  have b1 : (C₁ : ℝ) * s ^ 3 * (5 * X) ≤ 5 * C₁ * (X ^ 4 * As) := by
    have c : (s : ℝ) ^ 3 * X ≤ X ^ 4 :=
      calc (s : ℝ) ^ 3 * X ≤ X ^ 3 * X := by gcongr
        _ = X ^ 4 := by ring
    have c' := mul_le_mul_of_nonneg_left (c.trans hX4) (show (0 : ℝ) ≤ 5 * C₁ by linarith)
    calc (C₁ : ℝ) * s ^ 3 * (5 * X) = 5 * C₁ * ((s : ℝ) ^ 3 * X) := by ring
      _ ≤ _ := c'
  rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
  linarith

/- English proof (translation)
Introduce `C₁ C₂ Ca`. Use `⟨5 * (C₁ : ℝ) + 9 * Ca + Ca * C₂ + 11, ?_⟩` and prove the remaining obligations. Introduce `r n s As al A A₀ hn _ hs hAs hal hA₀ hA`. Use `set X : ℝ := (r : ℝ) + 1 with hXdef`. Establish `hr0 : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`.

Establish `hX1 : (1 : ℝ) ≤ X` using `by linarith`. Establish `hX0 : (0 : ℝ) ≤ X` using `by linarith`. Establish `hsX : (s : ℝ) ≤ X`. Establish `: (s : ℝ) ≤ (r : ℝ) + 1` using `by exact_mod_cast hs`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hrX : (r : ℝ) ≤ X` using `by linarith`. Establish `hn1 : (1 : ℝ) ≤ n`. Establish `: 1 ≤ n` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hAsR : (n : ℝ) ^ 3 ≤ As` using `by exact_mod_cast hAs`.

Establish `hn2 : (n : ℝ) ^ 2 ≤ As` using `(pow_le_pow_right₀ hn1 (show 2 ≤ 3 by norm_num)).trans hAsR`. Establish `hW1 : (1 : ℝ) ≤ As` using `(one_le_pow₀ hn1).trans hAsR`. Establish `halR : (al : ℝ) ≤ C₂ * (s : ℝ) ^ 2 + 1` using `by exact_mod_cast hal`. Establish `hC₁ : (0 : ℝ) ≤ C₁` using `Nat.cast_nonneg _`. Establish `hCa : (0 : ℝ) ≤ Ca` using `Nat.cast_nonneg _`.

Establish `hC₂ : (0 : ℝ) ≤ C₂` using `Nat.cast_nonneg _`. Establish `hs0 : (0 : ℝ) ≤ s` using `Nat.cast_nonneg _`. Establish `hal0 : (0 : ℝ) ≤ al` using `Nat.cast_nonneg _`. Establish `hX4p : (1 : ℝ) ≤ X ^ 4` using `one_le_pow₀ hX1`. Establish `hT1 : (1 : ℝ) ≤ X ^ 4 * As` using `one_le_mul_of_one_le_of_one_le hX4p hW1`.

Establish `hX3 : X ^ 3 ≤ X ^ 4` using `pow_le_pow_right₀ hX1 (by norm_num)`. Establish `hX2 : X ^ 2 ≤ X ^ 4` using `pow_le_pow_right₀ hX1 (by norm_num)`. Establish `hXX : X ≤ X ^ 4` using `by simpa using pow_le_pow_right₀ hX1 (show 1 ≤ 4 by norm_num)`. Establish `hX4 : X ^ 4 ≤ X ^ 4 * As` using `le_mul_of_one_le_right (by positivity) hW1`. Establish `hX3T : X ^ 3 ≤ X ^ 4 * As` using `hX3.trans hX4`.

Establish `hWT : (As : ℝ) ≤ X ^ 4 * As` using `le_mul_of_one_le_left (by linarith) hX4p`. Establish `hXW : X * As ≤ X ^ 4 * As` using `mul_le_mul_of_nonneg_right hXX (by linarith)`. Establish `b2 : (Ca : ℝ) * r ^ 2 * (5 * X) ≤ 5 * Ca * (X ^ 4 * As)`. Establish `c : (r : ℝ) ^ 2 * X ≤ X ^ 3`. Combine the equalities or inequalities in the displayed calculation.

Establish `c'` using `mul_le_mul_of_nonneg_left (c.trans hX3T) (show (0 : ℝ) ≤ 5 * Ca by linarith)`. Combine the equalities or inequalities in the displayed calculation. Establish `b3 : (Ca : ℝ) * ((n : ℝ) ^ 2 + (r : ℝ) ^ 3 + (r : ℝ) * (al : ℝ)) ≤ (Ca * (3 + C₂)) * (X ^ 4 * As)`. Establish `c1 : (r : ℝ) ^ 3 ≤ X ^ 3` using `by gcongr`. Establish `hss : (s : ℝ) ^ 2 ≤ X ^ 2` using `by gcongr`.

Establish `c2a : (al : ℝ) ≤ C₂ * X ^ 2 + 1` using `by linarith [mul_le_mul_of_nonneg_left hss hC₂]`. Establish `c2 : (r : ℝ) * al ≤ X * (C₂ * X ^ 2 + 1)` using `mul_le_mul hrX c2a hal0 hX0`. Establish `c3 : X * (C₂ * X ^ 2 + 1) = C₂ * X ^ 3 + X` using `by ring`. Establish `c4` using `mul_le_mul_of_nonneg_left hX3T hC₂`. Establish `c5 : X ≤ X ^ 4 * As` using `hXX.trans hX4`.

Establish `: (n : ℝ) ^ 2 + (r : ℝ) ^ 3 + (r : ℝ) * (al : ℝ) ≤ (3 + C₂) * (X ^ 4 * As)`. Rewrite `c2` using `[c3]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `b4 : (Ca : ℝ) * r * As ≤ Ca * (X ^ 4 * As)`.

Use `mul_le_mul_of_nonneg_right hrX (show (0 : ℝ) ≤ As by linarith)` as an intermediate fact. Use `mul_le_mul_of_nonneg_left (this.trans hXW) hCa` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `b1 : (C₁ : ℝ) * s ^ 2 * (5 * X) ≤ 5 * C₁ * (X ^ 4 * As)`. Establish `c : (s : ℝ) ^ 2 * X ≤ X ^ 3`.

Combine the equalities or inequalities in the displayed calculation. Establish `c'` using `mul_le_mul_of_nonneg_left (c.trans hX3T) (show (0 : ℝ) ≤ 5 * C₁ by linarith)`. Combine the equalities or inequalities in the displayed calculation. Establish `b5 : 2 * X ^ 2 * (5 * X) ≤ 10 * (X ^ 4 * As)` using `by linarith`. Rewrite using `[lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem budgetTopConv : BudgetTopConv := by
  intro C₁ C₂ Ca
  refine ⟨5 * (C₁ : ℝ) + 9 * Ca + Ca * C₂ + 11, ?_⟩
  intro r n s As al A A₀ hn _ hs hAs hal hA₀ hA
  set X : ℝ := (r : ℝ) + 1 with hXdef
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hsX : (s : ℝ) ≤ X := by
    have : (s : ℝ) ≤ (r : ℝ) + 1 := by exact_mod_cast hs
    linarith
  have hrX : (r : ℝ) ≤ X := by linarith
  have hn1 : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hAsR : (n : ℝ) ^ 3 ≤ As := by exact_mod_cast hAs
  have hn2 : (n : ℝ) ^ 2 ≤ As := (pow_le_pow_right₀ hn1 (show 2 ≤ 3 by norm_num)).trans hAsR
  have hW1 : (1 : ℝ) ≤ As := (one_le_pow₀ hn1).trans hAsR
  have halR : (al : ℝ) ≤ C₂ * (s : ℝ) ^ 2 + 1 := by exact_mod_cast hal
  have hC₁ : (0 : ℝ) ≤ C₁ := Nat.cast_nonneg _
  have hCa : (0 : ℝ) ≤ Ca := Nat.cast_nonneg _
  have hC₂ : (0 : ℝ) ≤ C₂ := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hal0 : (0 : ℝ) ≤ al := Nat.cast_nonneg _
  have hX4p : (1 : ℝ) ≤ X ^ 4 := one_le_pow₀ hX1
  have hT1 : (1 : ℝ) ≤ X ^ 4 * As := one_le_mul_of_one_le_of_one_le hX4p hW1
  have hX3 : X ^ 3 ≤ X ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
  have hX2 : X ^ 2 ≤ X ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
  have hXX : X ≤ X ^ 4 := by simpa using pow_le_pow_right₀ hX1 (show 1 ≤ 4 by norm_num)
  have hX4 : X ^ 4 ≤ X ^ 4 * As := le_mul_of_one_le_right (by positivity) hW1
  have hX3T : X ^ 3 ≤ X ^ 4 * As := hX3.trans hX4
  have hWT : (As : ℝ) ≤ X ^ 4 * As := le_mul_of_one_le_left (by linarith) hX4p
  have hXW : X * As ≤ X ^ 4 * As := mul_le_mul_of_nonneg_right hXX (by linarith)
  have b2 : (Ca : ℝ) * r ^ 2 * (5 * X) ≤ 5 * Ca * (X ^ 4 * As) := by
    have c : (r : ℝ) ^ 2 * X ≤ X ^ 3 :=
      calc (r : ℝ) ^ 2 * X ≤ X ^ 2 * X := by gcongr
        _ = X ^ 3 := by ring
    have c' := mul_le_mul_of_nonneg_left (c.trans hX3T) (show (0 : ℝ) ≤ 5 * Ca by linarith)
    calc (Ca : ℝ) * r ^ 2 * (5 * X) = 5 * Ca * ((r : ℝ) ^ 2 * X) := by ring
      _ ≤ _ := c'
  have b3 : (Ca : ℝ) * ((n : ℝ) ^ 2 + (r : ℝ) ^ 3 + (r : ℝ) * (al : ℝ)) ≤ (Ca * (3 + C₂)) * (X ^ 4 * As) := by
    have c1 : (r : ℝ) ^ 3 ≤ X ^ 3 := by gcongr
    have hss : (s : ℝ) ^ 2 ≤ X ^ 2 := by gcongr
    have c2a : (al : ℝ) ≤ C₂ * X ^ 2 + 1 := by linarith [mul_le_mul_of_nonneg_left hss hC₂]
    have c2 : (r : ℝ) * al ≤ X * (C₂ * X ^ 2 + 1) := mul_le_mul hrX c2a hal0 hX0
    have c3 : X * (C₂ * X ^ 2 + 1) = C₂ * X ^ 3 + X := by ring
    have c4 := mul_le_mul_of_nonneg_left hX3T hC₂
    have c5 : X ≤ X ^ 4 * As := hXX.trans hX4
    have : (n : ℝ) ^ 2 + (r : ℝ) ^ 3 + (r : ℝ) * (al : ℝ) ≤ (3 + C₂) * (X ^ 4 * As) := by
      rw [c3] at c2
      linarith
    calc (Ca : ℝ) * ((n : ℝ) ^ 2 + (r : ℝ) ^ 3 + (r : ℝ) * (al : ℝ))
        ≤ Ca * ((3 + C₂) * (X ^ 4 * As)) := mul_le_mul_of_nonneg_left this hCa
      _ = _ := by ring
  have b4 : (Ca : ℝ) * r * As ≤ Ca * (X ^ 4 * As) := by
    have := mul_le_mul_of_nonneg_right hrX (show (0 : ℝ) ≤ As by linarith)
    have := mul_le_mul_of_nonneg_left (this.trans hXW) hCa
    linarith
  have b1 : (C₁ : ℝ) * s ^ 2 * (5 * X) ≤ 5 * C₁ * (X ^ 4 * As) := by
    have c : (s : ℝ) ^ 2 * X ≤ X ^ 3 :=
      calc (s : ℝ) ^ 2 * X ≤ X ^ 2 * X := by gcongr
        _ = X ^ 3 := by ring
    have c' := mul_le_mul_of_nonneg_left (c.trans hX3T) (show (0 : ℝ) ≤ 5 * C₁ by linarith)
    calc (C₁ : ℝ) * s ^ 2 * (5 * X) = 5 * C₁ * ((s : ℝ) ^ 2 * X) := by ring
      _ ≤ _ := c'
  have b5 : 2 * X ^ 2 * (5 * X) ≤ 10 * (X ^ 4 * As) := by linarith
  rw [lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]
  linarith

/- English proof (translation)
Introduce `s k V _ _ Φ A K Kd hs hA hK hKd h Z hZ`. Establish `hdet : G.detM Z ≠ 0` using `fun e => hKd (by rw [← e]; exact hZ)`. Take `⟨hc, hb⟩` from `h Z hdet`. Establish `hZ0 : Z ≠ 0`. Introduce and unpack `rfl`.

Apply `hdet` to reduce the goal to its premises. Use `haveI : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩`. Simplify using `only [G.detM]`. Conclude with `Matrix.det_zero`. Establish `hpos : 0 < ‖Z‖` using `norm_pos_iff.mpr hZ0`.

Conclude with `⟨hc, fun j hj => (hb j hj).trans (mul_le_mul_of_nonneg_left (decayMin _ _ hpos hA) hK)⟩`.
-/
theorem derivBoundOfDecay : DerivBoundOfDecay := by
  intro s k V _ _ Φ A K Kd hs hA hK hKd h Z hZ
  have hdet : G.detM Z ≠ 0 := fun e => hKd (by rw [← e]; exact hZ)
  obtain ⟨hc, hb⟩ := h Z hdet
  have hZ0 : Z ≠ 0 := by
    rintro rfl
    apply hdet
    haveI : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
    simp only [G.detM]
    exact Matrix.det_zero
  have hpos : 0 < ‖Z‖ := norm_pos_iff.mpr hZ0
  exact ⟨hc, fun j hj => (hb j hj).trans (mul_le_mul_of_nonneg_left (decayMin _ _ hpos hA) hK)⟩

/- English proof (translation)
Introduce `s k V V' _ _ _ _ T Φ Kd bd h Z hZ`. Take `⟨hc, hb⟩` from `h Z hZ`. Establish `hc' : ContDiffAt ℝ k (fun Z => T (Φ Z)) Z` using `(T.restrictScalars ℝ).contDiff.contDiffAt.comp Z hc`. Use `⟨hc', fun j hj => ?_⟩` and prove the remaining obligations. Establish `k1 : ‖iteratedFDeriv ℝ j (fun y => (T.restrictScalars ℝ) (Φ y)) Z‖ ≤ ‖T.restrictScalars ℝ‖ * ‖iteratedFDeriv ℝ j Φ Z‖` using `(T.restrictScalars ℝ).norm_iteratedFDeriv_comp_left hc (by exact_mod_cast hj)`.

Rewrite `k1` using `[ContinuousLinearMap.norm_restrictScalars]`. Use `show _ ≤ ‖T‖ * bd Z`. Conclude with `k1.trans (mul_le_mul_of_nonneg_left (hb j hj) (norm_nonneg _))`.
-/
theorem derivBoundComp : DerivBoundComp := by
  intro s k V V' _ _ _ _ T Φ Kd bd h Z hZ
  obtain ⟨hc, hb⟩ := h Z hZ
  have hc' : ContDiffAt ℝ k (fun Z => T (Φ Z)) Z :=
    (T.restrictScalars ℝ).contDiff.contDiffAt.comp Z hc
  refine ⟨hc', fun j hj => ?_⟩
  have k1 : ‖iteratedFDeriv ℝ j (fun y => (T.restrictScalars ℝ) (Φ y)) Z‖ ≤
      ‖T.restrictScalars ℝ‖ * ‖iteratedFDeriv ℝ j Φ Z‖ :=
    (T.restrictScalars ℝ).norm_iteratedFDeriv_comp_left hc (by exact_mod_cast hj)
  rw [ContinuousLinearMap.norm_restrictScalars] at k1
  show _ ≤ ‖T‖ * bd Z
  exact k1.trans (mul_le_mul_of_nonneg_left (hb j hj) (norm_nonneg _))

end Formalism.FourierDecayAlt.P.Ux7

open Formalism.FourierDecayAlt.P.Ux7 in
/- English proof (translation)
Conclude with `budgetWord`.
-/
theorem Formalism.FourierDecayAlt.P.budget_word : Formalism.FourierDecayAlt.U.BudgetWord := by
  exact budgetWord
open Formalism.FourierDecayAlt.P.Ux7 in
/- English proof (translation)
Conclude with `budgetWordStar`.
-/
theorem Formalism.FourierDecayAlt.P.budget_word_star : Formalism.FourierDecayAlt.U.BudgetWordStar := by
  exact budgetWordStar
open Formalism.FourierDecayAlt.P.Ux7 in
/- English proof (translation)
Conclude with `budget_second_corollary_holds`.
-/
theorem Formalism.FourierDecayAlt.P.budget_second_corollary : Formalism.FourierDecayAlt.U.DerivativeBudgetCount := by
  exact budget_second_corollary_holds
open Formalism.FourierDecayAlt.P.Ux7 in
/- English proof (translation)
Conclude with `thresholds_second_corollary_holds`.
-/
theorem Formalism.FourierDecayAlt.P.thresholds_second_corollary : Formalism.FourierDecayAlt.U.GermThresholds := by
  exact thresholds_second_corollary_holds
open Formalism.FourierDecayAlt.P.Ux7 in
/- English proof (translation)
Conclude with `budgetTop`.
-/
theorem Formalism.FourierDecayAlt.P.budget_top_level : Formalism.FourierDecayAlt.U.BudgetTop := by
  exact budgetTop
open Formalism.FourierDecayAlt.P.Ux7 in
/- English proof (translation)
Conclude with `budgetTopConv`.
-/
theorem Formalism.FourierDecayAlt.P.budget_top_convergence : Formalism.FourierDecayAlt.U.BudgetTopConv := by
  exact budgetTopConv
open Formalism.FourierDecayAlt.P.Ux7 in
/- English proof (translation)
Conclude with `decayMin`.
-/
theorem Formalism.FourierDecayAlt.P.decay_minimum : Formalism.FourierDecayAlt.U.DecayMin := by
  exact decayMin
open Formalism.FourierDecayAlt.P.Ux7 in
/- English proof (translation)
Conclude with `scaleMatch`.
-/
theorem Formalism.FourierDecayAlt.P.scale_matching : Formalism.FourierDecayAlt.U.ScaleMatch := by
  exact scaleMatch
open Formalism.FourierDecayAlt.P.Ux7 in
/- English proof (translation)
Conclude with `powerMatch`.
-/
theorem Formalism.FourierDecayAlt.P.power_matching : Formalism.FourierDecayAlt.U.PowerMatch := by
  exact powerMatch
open Formalism.FourierDecayAlt.P.Ux7 in
/- English proof (translation)
Conclude with `derivBoundOfDecay`.
-/
theorem Formalism.FourierDecayAlt.P.derivative_bound_of_decay : Formalism.FourierDecayAlt.U.DerivBoundOfDecay := by
  exact derivBoundOfDecay
open Formalism.FourierDecayAlt.P.Ux7 in
/- English proof (translation)
Conclude with `derivBoundComp`.
-/
theorem Formalism.FourierDecayAlt.P.derivative_bound_composition : Formalism.FourierDecayAlt.U.DerivBoundComp := by
  exact derivBoundComp
