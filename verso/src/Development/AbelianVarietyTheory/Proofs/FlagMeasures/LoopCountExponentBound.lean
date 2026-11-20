import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `C₁ Ad hC₁`. Establish `ha3 : (3 : ℝ) ≤ max Ad 3` using `le_max_right _ _`. Establish `haA : Ad ≤ max Ad 3` using `le_max_left _ _`. Generalize the expression as in `max Ad 3 = a at ha3 haA ⊢`. Establish `hb : (0 : ℝ) ≤ (a + 1) * C₁` using `by positivity`.

Use `⟨5 * a + (a + 1) * C₁, by linarith, ?_⟩` and prove the remaining obligations. Introduce `C hC s r f De NT HH hs hf hDe hNT hHH hDA hN`. Establish `hs' : (1 : ℝ) ≤ s` using `by exact_mod_cast hs`. Establish `hf' : (1 : ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hr' : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`.

Establish `hH0 : 0 < HH` using `by linarith`. Establish `hlf0 : 0 ≤ Real.log f` using `Real.log_nonneg hf'`. Establish `hl2 : 0 < Real.log 2` using `Real.log_pos (by norm_num)`. Establish `hl21 : Real.log 2 ≤ 1`. Use `Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith` as an intermediate fact.

Establish `hlfL : Real.log f ≤ Real.logb 2 (2 * f)`. Rewrite using `[Real.logb, le_div_iff₀ hl2, Real.log_mul (by norm_num) (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hL0 : 0 ≤ Real.logb 2 (2 * (f : ℝ))` using `le_trans hlf0 hlfL`. Generalize the expression as in `Real.logb 2 (2 * (f : ℝ)) = L at hlfL hL0 ⊢`.

Generalize the expression as in `Real.log (f : ℝ) = l at hlfL hlf0 ⊢`. Establish `hDa : De ≤ HH ^ a` using `hDA.trans (Real.rpow_le_rpow_of_exponent_le hHH haA)`. Establish `hDN : De * NT ≤ HH ^ (a + 1)`. Rewrite using `[Real.rpow_add hH0, Real.rpow_one]`. Conclude with `mul_le_mul hDa hN (by linarith) (by positivity)`.

Establish `h1 : De ^ (4 + L) ≤ HH ^ (a * (4 + L))`. Rewrite using `[Real.rpow_mul hH0.le]`. Conclude with `Real.rpow_le_rpow (by linarith) hDa (by linarith)`. Establish `h2 : (De * NT) ^ (C₁ * s + C₁ * l) ≤ HH ^ ((a + 1) * (C₁ * s + C₁ * l))`. Rewrite using `[Real.rpow_mul hH0.le]`.

Conclude with `Real.rpow_le_rpow (by positivity) hDN (by positivity)`. Establish `h3 : ((HH ^ a) ^ (3 * r + 5 * s + 5 * s * r + 2 * r ^ 2)) ^ 2 = HH ^ (a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2)))`. Rewrite using `[← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hH0.le]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hC3 : (3 : ℝ) ≤ C * s * f`. Establish `h0 : (3 : ℝ) ≤ C` using `by linarith`. Establish `: (3 : ℝ) ≤ C * s` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h4 : ((9 : ℝ) ^ (s * f)) ^ 2 ≤ (C * s * f) ^ (6 * s * f)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ 3 ^ (6 * s * f) := pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.zero_le (s * f)])`. Use `_ ≤ _ := pow_le_pow_left₀ (by norm_num) hC3 _`. Establish `hexp : a * (4 + L) + (a + 1) * (C₁ * s + C₁ * l) + a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2)) ≤ C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) + C * (1 + L)` using `by set P : ℝ := ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) with hP`. Establish `hsr : (0 : ℝ) ≤ s * r` using `by positivity`. Establish `hrr : (0 : ℝ) ≤ r ^ 2` using `by positivity`.

Establish `e1 : (s : ℝ) ≤ P` using `by rw [hP]; nlinarith`. Establish `e2 : 2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2) ≤ 5 * P` using `by rw [hP]; nlinarith`. Establish `hP0 : 0 ≤ P` using `by linarith`. Establish `e3 : (5 * a + (a + 1) * C₁) * P ≤ C * P` using `mul_le_mul_of_nonneg_right hC hP0`. Establish `e4 : (5 * a + (a + 1) * C₁) * (1 + L) ≤ C * (1 + L)` using `mul_le_mul_of_nonneg_right hC (by linarith)`.

Establish `e5 : (a + 1) * C₁ * s ≤ (a + 1) * C₁ * P` using `mul_le_mul_of_nonneg_left e1 hb`. Establish `e6 : (a + 1) * C₁ * l ≤ (a + 1) * C₁ * (1 + L)` using `mul_le_mul_of_nonneg_left (by linarith) hb`. Establish `e7` using `mul_le_mul_of_nonneg_left e2 (show 0 ≤ a by linarith)`. Establish `e8 : a * (4 + L) ≤ a * (5 * (1 + L))` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Establish `e9 : C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) = C * P` using `by rw [hP]; ring`.

Rewrite using `[e9]`. Use `clear_value P`. Take the linear combination `e3 + e4 + e5 + e6 + e7 + e8`. Rewrite using `[mul_pow, h3]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Real.rpow_add hH0, Real.rpow_add hH0]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hHH hexp) (by positivity)`.
-/
theorem loop_count_exponent_bound : ∀ C₁ Ad : ℝ, 1 ≤ C₁ → ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C ≥ C₀, ∀ (s r f : ℕ) (De NT HH : ℝ), 1 ≤ s → 1 ≤ f → 1 ≤ De → 1 ≤ NT → 1 ≤ HH → De ≤ HH ^ Ad → NT ≤ HH → De ^ (4 + Real.logb 2 (2 * f)) * (De * NT) ^ (C₁ * s + C₁ * Real.log f) * (9 ^ (s * f) * (HH ^ (max Ad 3)) ^ (3 * r + 5 * s + 5 * s * r + 2 * r ^ 2)) ^ 2 ≤ HH ^ (C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) + C * (1 + Real.logb 2 (2 * f))) * (C * s * f) ^ (6 * s * f) := by
  intro C₁ Ad hC₁
  have ha3 : (3 : ℝ) ≤ max Ad 3 := le_max_right _ _
  have haA : Ad ≤ max Ad 3 := le_max_left _ _
  generalize max Ad 3 = a at ha3 haA ⊢
  have hb : (0 : ℝ) ≤ (a + 1) * C₁ := by positivity
  refine ⟨5 * a + (a + 1) * C₁, by linarith, ?_⟩
  intro C hC s r f De NT HH hs hf hDe hNT hHH hDA hN
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hH0 : 0 < HH := by linarith
  have hlf0 : 0 ≤ Real.log f := Real.log_nonneg hf'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hlfL : Real.log f ≤ Real.logb 2 (2 * f) := by
    rw [Real.logb, le_div_iff₀ hl2, Real.log_mul (by norm_num) (by linarith)]
    nlinarith
  have hL0 : 0 ≤ Real.logb 2 (2 * (f : ℝ)) := le_trans hlf0 hlfL
  generalize Real.logb 2 (2 * (f : ℝ)) = L at hlfL hL0 ⊢
  generalize Real.log (f : ℝ) = l at hlfL hlf0 ⊢
  have hDa : De ≤ HH ^ a := hDA.trans (Real.rpow_le_rpow_of_exponent_le hHH haA)
  have hDN : De * NT ≤ HH ^ (a + 1) := by
    rw [Real.rpow_add hH0, Real.rpow_one]
    exact mul_le_mul hDa hN (by linarith) (by positivity)
  have h1 : De ^ (4 + L) ≤ HH ^ (a * (4 + L)) := by
    rw [Real.rpow_mul hH0.le]
    exact Real.rpow_le_rpow (by linarith) hDa (by linarith)
  have h2 : (De * NT) ^ (C₁ * s + C₁ * l) ≤ HH ^ ((a + 1) * (C₁ * s + C₁ * l)) := by
    rw [Real.rpow_mul hH0.le]
    exact Real.rpow_le_rpow (by positivity) hDN (by positivity)
  have h3 : ((HH ^ a) ^ (3 * r + 5 * s + 5 * s * r + 2 * r ^ 2)) ^ 2
      = HH ^ (a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2))) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hH0.le]
    congr 1
    push_cast
    ring
  have hC3 : (3 : ℝ) ≤ C * s * f := by
    have h0 : (3 : ℝ) ≤ C := by linarith
    have : (3 : ℝ) ≤ C * s := by nlinarith
    nlinarith
  have h4 : ((9 : ℝ) ^ (s * f)) ^ 2 ≤ (C * s * f) ^ (6 * s * f) := by
    calc ((9 : ℝ) ^ (s * f)) ^ 2 = 3 ^ (4 * (s * f)) := by
          rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
          congr 1; ring
      _ ≤ 3 ^ (6 * s * f) := pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.zero_le (s * f)])
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hC3 _
  have hexp : a * (4 + L) + (a + 1) * (C₁ * s + C₁ * l)
      + a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2))
      ≤ C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) + C * (1 + L) := by
    set P : ℝ := ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) with hP
    have hsr : (0 : ℝ) ≤ s * r := by positivity
    have hrr : (0 : ℝ) ≤ r ^ 2 := by positivity
    have e1 : (s : ℝ) ≤ P := by rw [hP]; nlinarith
    have e2 : 2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2) ≤ 5 * P := by rw [hP]; nlinarith
    have hP0 : 0 ≤ P := by linarith
    have e3 : (5 * a + (a + 1) * C₁) * P ≤ C * P := mul_le_mul_of_nonneg_right hC hP0
    have e4 : (5 * a + (a + 1) * C₁) * (1 + L) ≤ C * (1 + L) :=
      mul_le_mul_of_nonneg_right hC (by linarith)
    have e5 : (a + 1) * C₁ * s ≤ (a + 1) * C₁ * P := mul_le_mul_of_nonneg_left e1 hb
    have e6 : (a + 1) * C₁ * l ≤ (a + 1) * C₁ * (1 + L) := mul_le_mul_of_nonneg_left (by linarith) hb
    have e7 := mul_le_mul_of_nonneg_left e2 (show 0 ≤ a by linarith)
    have e8 : a * (4 + L) ≤ a * (5 * (1 + L)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e9 : C * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) = C * P := by rw [hP]; ring
    rw [e9]
    clear_value P
    linear_combination e3 + e4 + e5 + e6 + e7 + e8
  rw [mul_pow, h3]
  calc _ ≤ HH ^ (a * (4 + L)) * HH ^ ((a + 1) * (C₁ * s + C₁ * l)) *
        ((C * s * f) ^ (6 * s * f) * HH ^ (a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2)))) := by
        gcongr
    _ = HH ^ (a * (4 + L) + (a + 1) * (C₁ * s + C₁ * l)
      + a * (2 * (3 * (r : ℝ) + 5 * s + 5 * s * r + 2 * r ^ 2))) * (C * s * f) ^ (6 * s * f) := by
        rw [Real.rpow_add hH0, Real.rpow_add hH0]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hHH hexp) (by positivity)

end GlobalTheory
