import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Establish `h` using `Nat.pow_succ_le_ascFactorial (n + 1) A`. Rewrite `h` using `[Nat.ascFactorial_eq_factorial_mul_choose]`. Conclude with `h` after adjusting the coercions.
-/
lemma pow_succ_le_factorial_mul_choose (n A : ℕ) :
    ((n : ℝ) + 1) ^ A ≤ (A.factorial : ℝ) * ((n + A).choose A : ℕ) := by
  have h := Nat.pow_succ_le_ascFactorial (n + 1) A
  rw [Nat.ascFactorial_eq_factorial_mul_choose] at h
  exact_mod_cast h

/- English proof (translation)
Rewrite using `[Complex.norm_exp, ← Real.exp_nat_mul]`. Use `congr 1`. Simplify using `[Complex.mul_re, Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma norm_qterm (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = Real.exp (-2 * π * τ.im) ^ n := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

/- English proof (translation)
Use `set t := 2 * π * y with ht`. Establish `htpos : 0 < t` using `by positivity`. Establish `hty : y ≤ t`. Establish `: (1 : ℝ) ≤ 2 * π` using `by nlinarith [Real.pi_gt_three]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `h1 : Real.exp (-t) ≤ (1 + t)⁻¹`. Rewrite using `[Real.exp_neg]`. Conclude with `inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp t])`. Establish `h2 : t / (1 + t) ≤ 1 - Real.exp (-t)`. Establish `: t / (1 + t) = 1 - (1 + t)⁻¹` using `by field_simp; ring`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : (1 - Real.exp (-t))⁻¹ ≤ (t / (1 + t))⁻¹` using `inv_anti₀ (by positivity) h2`. Establish `h4 : (t / (1 + t))⁻¹ = 1 + t⁻¹` using `by field_simp; ring`. Establish `h5 : t⁻¹ ≤ y⁻¹` using `inv_anti₀ hy hty`. Establish `: -2 * π * y = -t` using `by rw [ht]; ring`.

Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma one_sub_exp_inv_le (y : ℝ) (hy : 0 < y) :
    (1 - Real.exp (-2 * π * y))⁻¹ ≤ 1 + y⁻¹ := by
  set t := 2 * π * y with ht
  have htpos : 0 < t := by positivity
  have hty : y ≤ t := by
    have : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
    nlinarith
  have h1 : Real.exp (-t) ≤ (1 + t)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp t])
  have h2 : t / (1 + t) ≤ 1 - Real.exp (-t) := by
    have : t / (1 + t) = 1 - (1 + t)⁻¹ := by field_simp; ring
    linarith
  have h3 : (1 - Real.exp (-t))⁻¹ ≤ (t / (1 + t))⁻¹ := inv_anti₀ (by positivity) h2
  have h4 : (t / (1 + t))⁻¹ = 1 + t⁻¹ := by field_simp; ring
  have h5 : t⁻¹ ≤ y⁻¹ := inv_anti₀ hy hty
  have : -2 * π * y = -t := by rw [ht]; ring
  rw [this]
  linarith

/- English proof (translation)
Break down `le_or_gt 1 y with h | h` into its components or cases. Establish `: 1 + y⁻¹ ≤ 2 * y`. Establish `: y⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ h`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Establish `: 0 ≤ (y ^ B)⁻¹` using `by positivity`. Use polynomial arithmetic with `[pow_pos (two_pos : (0:ℝ) < 2) B]`. Establish `: 1 + y⁻¹ ≤ 2 * y⁻¹`. Establish `: 1 ≤ y⁻¹` using `one_le_inv₀ hy |>.mpr h.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation. Establish `: 0 ≤ y ^ B` using `by positivity`. Use polynomial arithmetic with `[pow_pos (two_pos : (0:ℝ) < 2) B]`.
-/
lemma one_add_inv_pow_le (y : ℝ) (hy : 0 < y) (B : ℕ) :
    (1 + y⁻¹) ^ B ≤ 2 ^ B * (y ^ B + (y ^ B)⁻¹) := by
  rcases le_or_gt 1 y with h | h
  · have : 1 + y⁻¹ ≤ 2 * y := by
      have : y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
      linarith
    calc (1 + y⁻¹) ^ B ≤ (2 * y) ^ B := pow_le_pow_left₀ (by positivity) this B
      _ = 2 ^ B * y ^ B := mul_pow _ _ _
      _ ≤ 2 ^ B * (y ^ B + (y ^ B)⁻¹) := by
        have : 0 ≤ (y ^ B)⁻¹ := by positivity
        nlinarith [pow_pos (two_pos : (0:ℝ) < 2) B]
  · have : 1 + y⁻¹ ≤ 2 * y⁻¹ := by
      have : 1 ≤ y⁻¹ := one_le_inv₀ hy |>.mpr h.le
      linarith
    calc (1 + y⁻¹) ^ B ≤ (2 * y⁻¹) ^ B := pow_le_pow_left₀ (by positivity) this B
      _ = 2 ^ B * (y ^ B)⁻¹ := by rw [mul_pow, inv_pow]
      _ ≤ 2 ^ B * (y ^ B + (y ^ B)⁻¹) := by
        have : 0 ≤ y ^ B := by positivity
        nlinarith [pow_pos (two_pos : (0:ℝ) < 2) B]

/- English proof (translation)
Introduce `a ⟨C, A, hC⟩`. Establish `hC0 : 0 ≤ C`. Use `hC 0` as an intermediate fact. Simplify using `at this`. Conclude with `le_trans (norm_nonneg _) this`.

Use `⟨C * A.factorial * 2 ^ (A + 1), A + 1, fun τ => ?_⟩` and prove the remaining obligations. Use `set y := τ.im`. Establish `hy : 0 < y` using `τ.im_pos`. Use `set r := Real.exp (-2 * π * y) with hr`. Establish `hr0 : 0 < r` using `Real.exp_pos _`.

Establish `hr1 : r < 1`. Use `Real.pi_pos` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `hrn : ‖r‖ < 1` using `by rwa [Real.norm_of_nonneg hr0.le]`. Establish `hS` using `hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) A hrn`.

Establish `hbound : ∀ n : ℕ, ‖a n * cexp (2 * π * Complex.I * n * τ)‖ ≤ (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n)`. Introduce `n`. Rewrite using `[norm_mul, norm_qterm]`. Establish `h1` using `hC n`. Establish `h2` using `pow_succ_le_factorial_mul_choose n A`.

Combine the equalities or inequalities in the displayed calculation. Establish `hsum2 : HasSum (fun n : ℕ => (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n)) ((C * A.factorial) * (1 / (1 - r) ^ (A + 1)))` using `hS.mul_left _`. Establish `hsumm : Summable (fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖)` using `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hsum2.summable`. Establish `key : ‖qs a τ‖ ≤ (C * A.factorial) * (1 / (1 - r) ^ (A + 1))`. Unfold `qs`.

Combine the equalities or inequalities in the displayed calculation. Establish `hinv : 1 / (1 - r) ^ (A + 1) ≤ 2 ^ (A + 1) * (y ^ (A + 1) + (y ^ (A + 1))⁻¹)`. Rewrite using `[one_div, ← inv_pow]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mod_qs_of_polyB : ∀ a : ℕ → ℂ, PolyB a → Mod (qs a) := by
  intro a ⟨C, A, hC⟩
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp at this
    exact le_trans (norm_nonneg _) this
  refine ⟨C * A.factorial * 2 ^ (A + 1), A + 1, fun τ => ?_⟩
  set y := τ.im
  have hy : 0 < y := τ.im_pos
  set r := Real.exp (-2 * π * y) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    have := Real.pi_pos
    calc r < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
      _ = 1 := Real.exp_zero
  have hrn : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0.le]
  have hS := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) A hrn
  have hbound : ∀ n : ℕ, ‖a n * cexp (2 * π * Complex.I * n * τ)‖ ≤
      (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n) := by
    intro n
    rw [norm_mul, norm_qterm]
    have h1 := hC n
    have h2 := pow_succ_le_factorial_mul_choose n A
    calc ‖a n‖ * r ^ n ≤ C * ((n : ℝ) + 1) ^ A * r ^ n :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ C * ((A.factorial : ℝ) * ((n + A).choose A : ℕ)) * r ^ n := by
          gcongr
      _ = (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n) := by ring
  have hsum2 : HasSum (fun n : ℕ => (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n))
      ((C * A.factorial) * (1 / (1 - r) ^ (A + 1))) := hS.mul_left _
  have hsumm : Summable (fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hsum2.summable
  have key : ‖qs a τ‖ ≤ (C * A.factorial) * (1 / (1 - r) ^ (A + 1)) := by
    unfold qs
    calc ‖∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * τ)‖
        ≤ ∑' n : ℕ, ‖a n * cexp (2 * π * Complex.I * n * τ)‖ := norm_tsum_le_tsum_norm hsumm
      _ ≤ ∑' n : ℕ, (C * A.factorial) * (((n + A).choose A : ℕ) * r ^ n) :=
          hsumm.tsum_le_tsum hbound hsum2.summable
      _ = _ := hsum2.tsum_eq
  have hinv : 1 / (1 - r) ^ (A + 1) ≤ 2 ^ (A + 1) * (y ^ (A + 1) + (y ^ (A + 1))⁻¹) := by
    rw [one_div, ← inv_pow]
    calc ((1 - r)⁻¹) ^ (A + 1) ≤ (1 + y⁻¹) ^ (A + 1) :=
          pow_le_pow_left₀ (by have : 0 < 1 - r := by linarith
                               positivity) (one_sub_exp_inv_le y hy) _
      _ ≤ _ := one_add_inv_pow_le y hy _
  calc ‖qs a τ‖ ≤ (C * A.factorial) * (1 / (1 - r) ^ (A + 1)) := key
    _ ≤ (C * A.factorial) * (2 ^ (A + 1) * (y ^ (A + 1) + (y ^ (A + 1))⁻¹)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = C * A.factorial * 2 ^ (A + 1) * (y ^ (A + 1) + (y ^ (A + 1))⁻¹) := by ring

end GlobalTheory.EisM
