import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `q ρ a hq hρ`. Establish `hQ : (2:ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hQ0 : (0:ℝ) < q` using `by linarith`. Establish `hQ1 : (1:ℝ) ≤ q` using `by linarith`. Use `set r : ℝ := (q:ℝ) ^ (1 - (ρ:ℤ)) with hr`.

Establish `hr0 : 0 ≤ r` using `by positivity`. Establish `hr8 : r ≤ 1 / 8`. Establish `h1 : r ≤ (q:ℝ) ^ (-3:ℤ)` using `zpow_le_zpow_right₀ hQ1 (by omega)`. Establish `h2 : (q:ℝ) ^ (-3:ℤ) = ((q:ℝ) ^ 3)⁻¹` using `by norm_num [zpow_neg]`. Establish `h3 : (8:ℝ) ≤ (q:ℝ) ^ 3`.

Use `pow_le_pow_left₀ (by norm_num) hQ 3` as an intermediate fact. Evaluate the numerical expressions using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : ((q:ℝ) ^ 3)⁻¹ ≤ (8:ℝ)⁻¹` using `inv_anti₀ (by norm_num) h3`. Rewrite `h1` using `[h2]`.

Combine the linear relations using `[show (8:ℝ)⁻¹ = 1 / 8 by norm_num]`. Establish `key : ∀ i : ℕ, (q:ℝ) ^ i * (q:ℝ) ^ (-(i * ρ : ℤ)) = r ^ i`. Introduce `i`. Rewrite using `[hr, ← zpow_natCast ((q:ℝ)) i, ← zpow_natCast ((q:ℝ) ^ (1 - (ρ:ℤ))) i, ← zpow_mul, ← zpow_add₀ hQ0.ne']`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hterm : ∀ i ∈ Finset.Icc 1 a, ((q:ℝ) ^ i - (q:ℝ) ^ (i - 1)) * (q:ℝ) ^ (-(i * ρ : ℤ)) ≤ r ^ i`. Introduce `i _`. Rewrite using `[← key i]`.

Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Establish `: (0:ℝ) ≤ (q:ℝ) ^ (i - 1)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hgeom : ∑ i ∈ Finset.Icc 1 a, r ^ i ≤ r ^ 1 / (1 - r)`. Establish `hIcc : Finset.Icc 1 a = Finset.Ico 1 (a + 1)`.

Use extensionality with `i`. Simplify using `only [Finset.mem_Icc, Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hIcc]`. Conclude with `geom_sum_Ico_le_of_lt_one hr0 (by linarith)`.

Establish `hfrac : r ^ 1 / (1 - r) ≤ 8 / 7 * r`. Rewrite using `[pow_one, div_le_iff₀ (by linarith)]`. Use polynomial arithmetic with `[mul_nonneg hr0 (show (0:ℝ) ≤ 1 / 8 - r by linarith)]`. Combine the linear relations using `[Finset.sum_le_sum hterm]`. Introduce `j`.

Establish `main : ∀ n : ℕ, 1 + ∑ i ∈ Finset.Icc 1 n, ((q : ℝ) ^ i - (q : ℝ) ^ (i - 1)) * (q : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ)) ≤ (q:ℝ) ^ (min n j) + 1 / 7 * (q:ℝ) ^ j * (1 - (1 / 8 : ℝ) ^ (n - j))`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Rewrite using `[Finset.sum_Icc_succ_top (by omega), ← add_assoc]`. Break down `Nat.lt_or_ge n j with h | h` into its components or cases. Establish `e1 : n + 1 - j = 0` using `by omega`. Establish `e2 : n - j = 0` using `by omega`. Establish `e3 : min (n + 1) j = n + 1` using `by omega`.

Establish `e4 : min n j = n` using `by omega`. Rewrite using `[e1, e3, Nat.add_sub_cancel]`. Rewrite `ih` using `[e2, e4]`. Simplify using `only [Nat.cast_zero, zero_mul, neg_zero, zpow_zero, mul_one, pow_zero, sub_self, mul_zero, add_zero] at ih ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e1 : n + 1 - j = (n - j) + 1` using `by omega`. Establish `e3 : min (n + 1) j = j` using `by omega`. Establish `e4 : min n j = j` using `by omega`. Rewrite `ih` using `[e4]`. Rewrite using `[e3, Nat.add_sub_cancel]`.

Establish `hterm : ((q:ℝ) ^ (n + 1) - (q:ℝ) ^ n) * (q:ℝ) ^ (-(((n + 1 - j : ℕ) : ℤ) * ρ)) ≤ (q:ℝ) ^ j * ((1 / 8 : ℝ) ^ (n - j) * (1 / 8))`. Establish `hk` using `key ((n - j) + 1)`. Rewrite `hk` using `[← e1]`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises.

Establish `: (0:ℝ) ≤ (q:ℝ) ^ n` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = (q:ℝ) ^ j * ((q:ℝ) ^ (n + 1 - j) * (q:ℝ) ^ (-(((n + 1 - j : ℕ) : ℤ) * ρ))) := by`. Rewrite using `[← mul_assoc, ← pow_add]`. Use `congr 2`.

Use linear arithmetic over natural numbers and integers. Use `_ = (q:ℝ) ^ j * r ^ (n + 1 - j) := by rw [hk]`. Use `_ ≤ (q:ℝ) ^ j * ((1 / 8 : ℝ) ^ (n - j) * (1 / 8)) := by`. Rewrite using `[e1, ← pow_succ]`. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr8 _) (by positivity)`.

Establish `h8 : (1 / 8 : ℝ) ^ (n + 1 - j) = (1 / 8) ^ (n - j) * (1 / 8)`. Rewrite using `[e1, pow_succ]`. Rewrite using `[h8]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmin : (q:ℝ) ^ (min a j) ≤ (q:ℝ) ^ j` using `pow_le_pow_right₀ hQ1 (min_le_right _ _)`.

Establish `hX : (0:ℝ) ≤ (q:ℝ) ^ j` using `by positivity`. Establish `hY : (0:ℝ) ≤ (1 / 8 : ℝ) ^ (a - j)` using `by positivity`. Use polynomial arithmetic with `[main a, mul_nonneg hX hY]`.
-/
theorem two_geometric_sums_index_bound :
    ∀ (q ρ a : ℕ), 2 ≤ q → 4 ≤ ρ →
      (∑ i ∈ Finset.Icc 1 a, ((q : ℝ) ^ i - (q : ℝ) ^ (i - 1)) * (q : ℝ) ^ (-(i * ρ : ℤ))
        ≤ 8 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ))) ∧
      ∀ j : ℕ, 1 + ∑ i ∈ Finset.Icc 1 a,
        ((q : ℝ) ^ i - (q : ℝ) ^ (i - 1)) * (q : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ))
          ≤ 8 / 7 * (q : ℝ) ^ j := by
  intro q ρ a hq hρ
  have hQ : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hQ0 : (0:ℝ) < q := by linarith
  have hQ1 : (1:ℝ) ≤ q := by linarith
  set r : ℝ := (q:ℝ) ^ (1 - (ρ:ℤ)) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr8 : r ≤ 1 / 8 := by
    have h1 : r ≤ (q:ℝ) ^ (-3:ℤ) := zpow_le_zpow_right₀ hQ1 (by omega)
    have h2 : (q:ℝ) ^ (-3:ℤ) = ((q:ℝ) ^ 3)⁻¹ := by norm_num [zpow_neg]
    have h3 : (8:ℝ) ≤ (q:ℝ) ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) hQ 3
      norm_num at this
      linarith
    have h4 : ((q:ℝ) ^ 3)⁻¹ ≤ (8:ℝ)⁻¹ := inv_anti₀ (by norm_num) h3
    rw [h2] at h1
    linarith [show (8:ℝ)⁻¹ = 1 / 8 by norm_num]
  have key : ∀ i : ℕ, (q:ℝ) ^ i * (q:ℝ) ^ (-(i * ρ : ℤ)) = r ^ i := by
    intro i
    rw [hr, ← zpow_natCast ((q:ℝ)) i, ← zpow_natCast ((q:ℝ) ^ (1 - (ρ:ℤ))) i, ← zpow_mul,
      ← zpow_add₀ hQ0.ne']
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · have hterm : ∀ i ∈ Finset.Icc 1 a,
        ((q:ℝ) ^ i - (q:ℝ) ^ (i - 1)) * (q:ℝ) ^ (-(i * ρ : ℤ)) ≤ r ^ i := by
      intro i _
      rw [← key i]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have : (0:ℝ) ≤ (q:ℝ) ^ (i - 1) := by positivity
      linarith
    have hgeom : ∑ i ∈ Finset.Icc 1 a, r ^ i ≤ r ^ 1 / (1 - r) := by
      have hIcc : Finset.Icc 1 a = Finset.Ico 1 (a + 1) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hIcc]
      exact geom_sum_Ico_le_of_lt_one hr0 (by linarith)
    have hfrac : r ^ 1 / (1 - r) ≤ 8 / 7 * r := by
      rw [pow_one, div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg hr0 (show (0:ℝ) ≤ 1 / 8 - r by linarith)]
    linarith [Finset.sum_le_sum hterm]
  · intro j
    have main : ∀ n : ℕ, 1 + ∑ i ∈ Finset.Icc 1 n,
          ((q : ℝ) ^ i - (q : ℝ) ^ (i - 1)) * (q : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ))
          ≤ (q:ℝ) ^ (min n j) + 1 / 7 * (q:ℝ) ^ j * (1 - (1 / 8 : ℝ) ^ (n - j)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc]
        rcases Nat.lt_or_ge n j with h | h
        · have e1 : n + 1 - j = 0 := by omega
          have e2 : n - j = 0 := by omega
          have e3 : min (n + 1) j = n + 1 := by omega
          have e4 : min n j = n := by omega
          rw [e1, e3, Nat.add_sub_cancel]
          rw [e2, e4] at ih
          simp only [Nat.cast_zero, zero_mul, neg_zero, zpow_zero, mul_one, pow_zero, sub_self,
            mul_zero, add_zero] at ih ⊢
          linarith
        · have e1 : n + 1 - j = (n - j) + 1 := by omega
          have e3 : min (n + 1) j = j := by omega
          have e4 : min n j = j := by omega
          rw [e4] at ih
          rw [e3, Nat.add_sub_cancel]
          have hterm : ((q:ℝ) ^ (n + 1) - (q:ℝ) ^ n) * (q:ℝ) ^ (-(((n + 1 - j : ℕ) : ℤ) * ρ))
              ≤ (q:ℝ) ^ j * ((1 / 8 : ℝ) ^ (n - j) * (1 / 8)) := by
            have hk := key ((n - j) + 1)
            rw [← e1] at hk
            calc ((q:ℝ) ^ (n + 1) - (q:ℝ) ^ n) * (q:ℝ) ^ (-(((n + 1 - j : ℕ) : ℤ) * ρ))
                ≤ (q:ℝ) ^ (n + 1) * (q:ℝ) ^ (-(((n + 1 - j : ℕ) : ℤ) * ρ)) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  have : (0:ℝ) ≤ (q:ℝ) ^ n := by positivity
                  linarith
              _ = (q:ℝ) ^ j * ((q:ℝ) ^ (n + 1 - j) * (q:ℝ) ^ (-(((n + 1 - j : ℕ) : ℤ) * ρ))) := by
                  rw [← mul_assoc, ← pow_add]
                  congr 2
                  omega
              _ = (q:ℝ) ^ j * r ^ (n + 1 - j) := by rw [hk]
              _ ≤ (q:ℝ) ^ j * ((1 / 8 : ℝ) ^ (n - j) * (1 / 8)) := by
                  rw [e1, ← pow_succ]
                  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr8 _) (by positivity)
          have h8 : (1 / 8 : ℝ) ^ (n + 1 - j) = (1 / 8) ^ (n - j) * (1 / 8) := by
            rw [e1, pow_succ]
          rw [h8]
          linarith
    have hmin : (q:ℝ) ^ (min a j) ≤ (q:ℝ) ^ j := pow_le_pow_right₀ hQ1 (min_le_right _ _)
    have hX : (0:ℝ) ≤ (q:ℝ) ^ j := by positivity
    have hY : (0:ℝ) ≤ (1 / 8 : ℝ) ^ (a - j) := by positivity
    nlinarith [main a, mul_nonneg hX hY]

end GlobalTheory
