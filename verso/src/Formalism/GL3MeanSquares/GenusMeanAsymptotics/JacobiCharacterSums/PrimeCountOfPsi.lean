import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTEOf
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTPiC

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

/- English proof (translation)
Introduce and unpack `⟨c, A, C₀, hc, hP⟩`. Take `⟨c₁, hc₁, hηl⟩` from `etaOf_lower 1 one_pos`. Use `⟨min (c / 2) (c ^ 2 / 2), 10 * |A| + 5632 * Real.exp (2 * min (c / 2) (c ^ 2 / 2)) / c₁, max (2 * C₀) 16, lt_min (by positivity) (by positivity), ?_⟩` and prove the remaining obligations. Introduce `M _ h8`. Use `⟨eOf M, fun p hp => eOf_exc M p hp, fun h χ₁ β₁ => eOf_none M h χ₁ β₁, ?_⟩` and prove the remaining obligations.

Introduce `X b hX2 hrange hb`. Establish `hMpos : 0 < M` using `Nat.pos_of_ne_zero (NeZero.ne M)`. Establish `hM8n : 8 ≤ M` using `Nat.le_of_dvd hMpos h8`. Establish `hM8 : (8 : ℝ) ≤ M` using `by exact_mod_cast hM8n`. Establish `hl2` using `Real.log_two_gt_d9`.

Establish `hl2'` using `Real.log_two_lt_d9`. Establish `hl : 2 ≤ Real.log M`. Establish `h88 : Real.log 8 = 3 * Real.log 2`. Rewrite using `[show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num`. Use `Real.log_le_log (by norm_num) hM8` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : Real.log 4 = 2 * Real.log 2`. Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num`. Establish `hll : 1 ≤ Real.log (Real.log M + 2)`. Use `Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ Real.log M + 2)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hprod : Real.log M ≤ Real.log M * Real.log (Real.log M + 2)` using `by nlinarith`. Establish `hprod0 : 0 ≤ Real.log M * Real.log (Real.log M + 2)` using `by linarith`. Establish `hrange' : max (2 * C₀) 16 * (Real.log M * Real.log (Real.log M + 2)) ≤ Real.log X`. Rewrite using `[← mul_assoc]`.

Conclude with `hrange`. Establish `hL16 : 16 * Real.log M ≤ Real.log X`. Use `mul_le_mul_of_nonneg_right (le_max_right (2 * C₀) 16) hprod0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLC : C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log X / 2`.

Use `mul_le_mul_of_nonneg_right (le_max_left (2 * C₀) 16) hprod0` as an intermediate fact. Establish `e : C₀ * Real.log M * Real.log (Real.log M + 2) = 2 * C₀ * (Real.log M * Real.log (Real.log M + 2)) / 2` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX0 : 0 < X` using `by linarith`.

Establish `hX4 : 4 ≤ X`. Rewrite using `[← Real.log_le_log_iff (by norm_num) hX0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs2 : 2 ≤ √X`. Rewrite using `[Real.le_sqrt' (by norm_num)]; linarith`.

Establish `hη0 : 0 ≤ etaOf M` using `(etaOf_pos M (by omega)).le`. Establish `hη1` using `etaOf_le_one M`. Establish `hηl'` using `hηl M (by omega)`. Establish `hP' : ∀ y : ℝ, √X ≤ y → y ≤ X → ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤ |A| * y * etaOf M * (Real.exp (-(c * Real.log y / Real.log M)) + Real.exp (-(c * Real.sqrt (Real.log y))))`. Introduce `y h1 h2`.

Establish `hy2 : 2 ≤ y` using `hs2.trans h1`. Establish `hly : Real.log X / 2 ≤ Real.log y`. Rewrite using `[← Real.log_sqrt hX0.le]`. Conclude with `Real.log_le_log (by linarith) h1`. Use `(hP M h8 y hy2 (by linarith)).trans ?_` and prove the remaining obligations.

Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)) hη0) (by positivity)`. Break down `he : eOf M with _ | ⟨χ₁, β₁⟩` into its components or cases. Rewrite `hP'` using `[he]`. Establish `e0 : mainAP (none : Option (DirichletCharacter ℂ M × ℝ)) b X = (liX X - 0 * liX (X ^ (1 : ℝ))) / (M.totient : ℝ)` using `by simp [mainAP]`. Rewrite using `[e0]`.

Conclude with `pi_core M h8 b hb none (by simp) (by norm_num) le_rfl (fun t _ => mainPsi_sum_none M b hb t 1) hη0 hη1 (Or.inl le_rfl) hc₁ hηl' hc (abs_nonneg A) hX0 hL16 hP'`. Rewrite `hP'` using `[he]`. Take `⟨_, _, _, hβlo, hβ1⟩` from `eOf_exc M _ he`. Establish `hχ` using `eOf_char_sq M χ₁ β₁ he b ((ZMod.isUnit_iff_coprime b M).mpr hb)`. Apply the tactic sequence `have hθ : |(χ₁ (b : ZMod M)).re| ≤ 1 := by rcases hχ with h | h <;> simp [h]`.

Establish `hβ : 1 / 2 ≤ β₁`. Establish `: 1 / (8 * Real.log M) ≤ 1 / 16`. Apply `one_div_le_one_div_of_le (by norm_num); linarith` to reduce the goal to its premises. Simplify using `only [] at hβlo`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hηe` using `etaOf_some M χ₁ β₁ he`. Establish `e1 : mainAP (some (χ₁, β₁)) b X = (liX X - (χ₁ (b : ZMod M)).re * liX (X ^ β₁)) / (M.totient : ℝ)` using `rfl`. Rewrite using `[e1]`. Conclude with `pi_core M h8 b hb (some (χ₁, β₁)) hθ hβ hβ1.le (fun t ht => mainPsi_sum_some M b hb χ₁ β₁ t ht hχ) hη0 hη1 (Or.inr (by rw [hηe]; exact min_le_right _ _)) hc₁ hηl' hc (abs_nonneg A) hX0 hL16 hP'`.
-/
theorem prime_count_of_psi : PiOf := by
  rintro ⟨c, A, C₀, hc, hP⟩
  obtain ⟨c₁, hc₁, hηl⟩ := etaOf_lower 1 one_pos
  refine ⟨min (c / 2) (c ^ 2 / 2), 10 * |A| + 5632 * Real.exp (2 * min (c / 2) (c ^ 2 / 2)) / c₁,
    max (2 * C₀) 16, lt_min (by positivity) (by positivity), ?_⟩
  intro M _ h8
  refine ⟨eOf M, fun p hp => eOf_exc M p hp, fun h χ₁ β₁ => eOf_none M h χ₁ β₁, ?_⟩
  intro X b hX2 hrange hb
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM8n : 8 ≤ M := Nat.le_of_dvd hMpos h8
  have hM8 : (8 : ℝ) ≤ M := by exact_mod_cast hM8n
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl : 2 ≤ Real.log M := by
    have h88 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hM8
    linarith
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hll : 1 ≤ Real.log (Real.log M + 2) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ Real.log M + 2)
    linarith
  have hprod : Real.log M ≤ Real.log M * Real.log (Real.log M + 2) := by nlinarith
  have hprod0 : 0 ≤ Real.log M * Real.log (Real.log M + 2) := by linarith
  have hrange' : max (2 * C₀) 16 * (Real.log M * Real.log (Real.log M + 2)) ≤ Real.log X := by
    rw [← mul_assoc]; exact hrange
  have hL16 : 16 * Real.log M ≤ Real.log X := by
    have := mul_le_mul_of_nonneg_right (le_max_right (2 * C₀) 16) hprod0
    linarith
  have hLC : C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log X / 2 := by
    have := mul_le_mul_of_nonneg_right (le_max_left (2 * C₀) 16) hprod0
    have e : C₀ * Real.log M * Real.log (Real.log M + 2) =
        2 * C₀ * (Real.log M * Real.log (Real.log M + 2)) / 2 := by ring
    rw [e]
    linarith
  have hX0 : 0 < X := by linarith
  have hX4 : 4 ≤ X := by
    rw [← Real.log_le_log_iff (by norm_num) hX0]
    linarith
  have hs2 : 2 ≤ √X := by
    rw [Real.le_sqrt' (by norm_num)]; linarith
  have hη0 : 0 ≤ etaOf M := (etaOf_pos M (by omega)).le
  have hη1 := etaOf_le_one M
  have hηl' := hηl M (by omega)
  have hP' : ∀ y : ℝ, √X ≤ y → y ≤ X →
      ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      |A| * y * etaOf M *
        (Real.exp (-(c * Real.log y / Real.log M)) + Real.exp (-(c * Real.sqrt (Real.log y)))) := by
    intro y h1 h2
    have hy2 : 2 ≤ y := hs2.trans h1
    have hly : Real.log X / 2 ≤ Real.log y := by
      rw [← Real.log_sqrt hX0.le]
      exact Real.log_le_log (by linarith) h1
    refine (hP M h8 y hy2 (by linarith)).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)) hη0) (by positivity)
  rcases he : eOf M with _ | ⟨χ₁, β₁⟩
  · rw [he] at hP'
    have e0 : mainAP (none : Option (DirichletCharacter ℂ M × ℝ)) b X =
        (liX X - 0 * liX (X ^ (1 : ℝ))) / (M.totient : ℝ) := by simp [mainAP]
    rw [e0]
    exact pi_core M h8 b hb none (by simp) (by norm_num) le_rfl
      (fun t _ => mainPsi_sum_none M b hb t 1) hη0 hη1 (Or.inl le_rfl) hc₁ hηl' hc (abs_nonneg A) hX0 hL16 hP'
  · rw [he] at hP'
    obtain ⟨_, _, _, hβlo, hβ1⟩ := eOf_exc M _ he
    have hχ := eOf_char_sq M χ₁ β₁ he b ((ZMod.isUnit_iff_coprime b M).mpr hb)
    have hθ : |(χ₁ (b : ZMod M)).re| ≤ 1 := by rcases hχ with h | h <;> simp [h]
    have hβ : 1 / 2 ≤ β₁ := by
      have : 1 / (8 * Real.log M) ≤ 1 / 16 := by
        apply one_div_le_one_div_of_le (by norm_num); linarith
      simp only [] at hβlo
      linarith
    have hηe := etaOf_some M χ₁ β₁ he
    have e1 : mainAP (some (χ₁, β₁)) b X =
        (liX X - (χ₁ (b : ZMod M)).re * liX (X ^ β₁)) / (M.totient : ℝ) := rfl
    rw [e1]
    exact pi_core M h8 b hb (some (χ₁, β₁)) hθ hβ hβ1.le
      (fun t ht => mainPsi_sum_some M b hb χ₁ β₁ t ht hχ) hη0 hη1
      (Or.inr (by rw [hηe]; exact min_le_right _ _)) hc₁ hηl' hc (abs_nonneg A) hX0 hL16 hP'

end Formalism.HermitianLattices.Ext.PrimesInProgressions
