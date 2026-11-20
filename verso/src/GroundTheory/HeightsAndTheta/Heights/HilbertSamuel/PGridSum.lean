import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Finset Filter Asymptotics

/- English proof (translation)
Proceed by induction on `m generalizing i with`. Consider the case `zero`. Apply the tactic sequence `cases i <;> cases j <;> simp <;> exact (Nat.choose_eq_zero_of_lt (by omega)).symm`. Consider the case `succ m ih`. Rewrite using `[Finset.Nat.sum_antidiagonal_succ]`.

Consider the cases of `i with`. Consider the case `zero`. Establish `h` using `ih 0`. Simplify using `only [Nat.choose_zero_right, one_mul, zero_add] at h ⊢`. Rewrite using `[h, Nat.choose_succ_succ (m + 1) j]`.

Consider the case `succ i`. Establish `h1` using `ih i`. Establish `h2` using `ih (i + 1)`. Establish `e : ∀ p : ℕ × ℕ, (p.1 + 1).choose (i + 1) * p.2.choose j = p.1.choose i * p.2.choose j + p.1.choose (i + 1) * p.2.choose j` using `fun p ↦ by`. Rewrite using `[Nat.choose_succ_succ', add_mul]`.

Simplify using `only [Nat.choose_zero_succ, zero_mul, zero_add, e, Finset.sum_add_distrib, h1, h2]`. Rewrite using `[show i + 1 + j + 1 = (i + j + 1) + 1 by omega, Nat.choose_succ_succ' (m + 1) (i + j + 1)]`.
-/
theorem GridSum.choose_antidiagonal (m i j : ℕ) :
    ∑ p ∈ antidiagonal m, p.1.choose i * p.2.choose j = (m + 1).choose (i + j + 1) := by
  induction m generalizing i with
  | zero =>
    cases i <;> cases j <;> simp <;> exact (Nat.choose_eq_zero_of_lt (by omega)).symm
  | succ m ih =>
    rw [Finset.Nat.sum_antidiagonal_succ]
    cases i with
    | zero =>
      have h := ih 0
      simp only [Nat.choose_zero_right, one_mul, zero_add] at h ⊢
      rw [h, Nat.choose_succ_succ (m + 1) j]
    | succ i =>
      have h1 := ih i
      have h2 := ih (i + 1)
      have e : ∀ p : ℕ × ℕ, (p.1 + 1).choose (i + 1) * p.2.choose j =
          p.1.choose i * p.2.choose j + p.1.choose (i + 1) * p.2.choose j := fun p ↦ by
        rw [Nat.choose_succ_succ', add_mul]
      simp only [Nat.choose_zero_succ, zero_mul, zero_add, e, Finset.sum_add_distrib, h1, h2]
      rw [show i + 1 + j + 1 = (i + j + 1) + 1 by omega, Nat.choose_succ_succ' (m + 1) (i + j + 1)]

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => simp`. Consider the case `succ m`. Rewrite using `[← GridSum.choose_antidiagonal m i j, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`. Simplify using the standard rewrite rules.
-/
theorem GridSum.choose_range (n i j : ℕ) :
    ∑ a ∈ range n, a.choose i * (n - 1 - a).choose j = n.choose (i + j + 1) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [← GridSum.choose_antidiagonal m i j, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp

/- English proof (translation)
Rewrite using `[le_div_iff₀ (by positivity)]`. Establish `h : a.choose i * i.factorial ≤ a ^ i`. Rewrite using `[mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]`. Conclude with `Nat.descFactorial_le_pow a i`. Conclude with `h` after adjusting the coercions.
-/
theorem GridSum.choose_le_pow_div_factorial (a i : ℕ) :
    (a.choose i : ℝ) ≤ (a : ℝ) ^ i / (i.factorial : ℝ) := by
  rw [le_div_iff₀ (by positivity)]
  have h : a.choose i * i.factorial ≤ a ^ i := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow a i
  exact_mod_cast h

/- English proof (translation)
Rewrite using `[div_le_iff₀ (by positivity)]`. Establish `h : a ^ i ≤ (a + i).choose i * i.factorial`. Rewrite using `[mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `h` after adjusting the coercions.
-/
theorem GridSum.pow_div_factorial_le (a i : ℕ) :
    (a : ℝ) ^ i / (i.factorial : ℝ) ≤ ((a + i).choose i : ℝ) := by
  rw [div_le_iff₀ (by positivity)]
  have h : a ^ i ≤ (a + i).choose i * i.factorial := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    calc a ^ i ≤ (a + i + 1 - i) ^ i := Nat.pow_le_pow_left (by omega) i
      _ ≤ (a + i).descFactorial i := Nat.pow_sub_le_descFactorial _ _
  exact_mod_cast h

/- English proof (translation)
Rewrite using `[← geom_sum₂_mul]`. Establish `hx : 0 ≤ x` using `hy.trans hxy`. Establish `hs : ∑ l ∈ range k, x ^ l * y ^ (k - 1 - l) ≤ k * x ^ (k - 1)`. Combine the equalities or inequalities in the displayed calculation. Apply `sum_le_sum` to reduce the goal to its premises.

Introduce `l hl`. Establish `hl' : l + (k - 1 - l) = k - 1` using `by have := mem_range.mp hl; omega`. Combine the equalities or inequalities in the displayed calculation. Use `_ = k * x ^ (k - 1) := by simp`. Establish `hd : 0 ≤ x - y` using `sub_nonneg.mpr hxy`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem GridSum.pow_sub_pow_le (x y : ℝ) (k : ℕ) (hy : 0 ≤ y) (hxy : y ≤ x) :
    x ^ k - y ^ k ≤ k * (x - y) * x ^ (k - 1) := by
  rw [← geom_sum₂_mul]
  have hx : 0 ≤ x := hy.trans hxy
  have hs : ∑ l ∈ range k, x ^ l * y ^ (k - 1 - l) ≤ k * x ^ (k - 1) := by
    calc ∑ l ∈ range k, x ^ l * y ^ (k - 1 - l) ≤ ∑ l ∈ range k, x ^ (k - 1) := by
          apply sum_le_sum
          intro l hl
          have hl' : l + (k - 1 - l) = k - 1 := by have := mem_range.mp hl; omega
          calc x ^ l * y ^ (k - 1 - l) ≤ x ^ l * x ^ (k - 1 - l) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hxy _) (pow_nonneg hx _)
            _ = x ^ (k - 1) := by rw [← pow_add, hl']
      _ = k * x ^ (k - 1) := by simp
  have hd : 0 ≤ x - y := sub_nonneg.mpr hxy
  calc (∑ l ∈ range k, x ^ l * y ^ (k - 1 - l)) * (x - y) ≤ (k * x ^ (k - 1)) * (x - y) :=
        mul_le_mul_of_nonneg_right hs hd
    _ = k * (x - y) * x ^ (k - 1) := by ring

/- English proof (translation)
Introduce `D i hi`. Use `set j := D - i with hj`. Establish `hD : i + j + 1 = D + 1` using `by omega`. Use `set F : ℝ := ((D + 1).factorial : ℝ) with hFdef`. Establish `hF1 : (1 : ℝ) ≤ F`.

Rewrite using `[hFdef]`. Conclude with `Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)` after adjusting the coercions. Establish `hF : 0 < F` using `lt_of_lt_of_le one_pos hF1`. Establish `lower : ∀ n : ℕ, ((n.choose (D + 1) : ℕ) : ℝ) ≤ ∑ a ∈ range n, (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ))`. Introduce `n`.

Establish `h` using `GridSum.choose_range n i j`. Rewrite `h` using `[hD]`. Rewrite using `[← h, Nat.cast_sum]`. Apply `sum_le_sum` to reduce the goal to its premises. Introduce `a _`.

Rewrite using `[mul_div_mul_comm, Nat.cast_mul]`. Conclude with `mul_le_mul (GridSum.choose_le_pow_div_factorial _ _) (GridSum.choose_le_pow_div_factorial _ _) (by positivity) (by positivity)`. Establish `upper : ∀ n : ℕ, ∑ a ∈ range n, (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) ≤ (((n + D).choose (D + 1) : ℕ) : ℝ)`. Introduce `n`. Establish `h` using `GridSum.choose_range (n + D) i j`.

Rewrite `h` using `[hD]`. Rewrite using `[← h, Nat.cast_sum]`. Combine the equalities or inequalities in the displayed calculation. Apply `sum_le_sum` to reduce the goal to its premises. Introduce `a ha`.

Establish `hb : n + D - 1 - (a + i) = (n - 1 - a) + j`. Use `mem_range.mp ha` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hb, mul_div_mul_comm, Nat.cast_mul]`. Conclude with `mul_le_mul (GridSum.pow_div_factorial_le _ _) (GridSum.pow_div_factorial_le _ _) (by positivity) (by positivity)`.

Use `_ = ∑ a ∈ (range n).map (addRightEmbedding i), ((a.choose i * (n + D - 1 - a).choose j : ℕ) : ℝ) := by`. Rewrite using `[sum_map]`. Both sides reduce to the same expression. Use `_ ≤ ∑ a ∈ range (n + D), ((a.choose i * (n + D - 1 - a).choose j : ℕ) : ℝ) := by`. Apply `sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises.

Introduce `x hx`. Rewrite `hx` using `[Finset.mem_map]`. Take `⟨a, ha, rfl⟩` from `hx`. Rewrite `ha`, the goal using `[mem_range]`. Express the relevant statement in the definitionally equal form `a + i < n + D`.

Use linear arithmetic over natural numbers and integers. Use `intros`. Check the signs of the components of the expression. Use `IsBigO.of_bound (((D + 1 : ℕ) : ℝ) * (2 * D) * 2 ^ D) ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop D] with n hn`.

Establish `hL` using `lower n`. Establish `hU` using `upper n`. Use `set S := ∑ a ∈ range n, (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) with hS`. Establish `hnD : (D : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `h1 : ((n : ℝ) - D) ^ (D + 1) ≤ ((n.choose (D + 1) : ℕ) : ℝ) * F`.

Establish `h : (n - D) ^ (D + 1) ≤ n.choose (D + 1) * (D + 1).factorial`. Rewrite using `[mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]`. Use `Nat.pow_sub_le_descFactorial n (D + 1)` as an intermediate fact. Rewrite `this` using `[show n + 1 - (D + 1) = n - D by omega]`. Then use the resulting hypothesis. Establish `h' : (((n - D : ℕ) : ℝ)) ^ (D + 1) ≤ ((n.choose (D + 1) : ℕ) : ℝ) * F`.

Rewrite using `[hFdef]`. Conclude with `h` after adjusting the coercions. Rewrite `h'` using `[Nat.cast_sub hn]`. Then use the resulting hypothesis. Establish `h2 : (((n + D).choose (D + 1) : ℕ) : ℝ) * F ≤ ((n : ℝ) + D) ^ (D + 1)`. Establish `h : (n + D).choose (D + 1) * (D + 1).factorial ≤ (n + D) ^ (D + 1)`.

Rewrite using `[mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]`. Conclude with `Nat.descFactorial_le_pow _ _`. Rewrite using `[hFdef]`. Conclude with `h` after adjusting the coercions. Establish `hSlo : ((n : ℝ) - D) ^ (D + 1) / F ≤ S`.

Rewrite using `[div_le_iff₀ hF]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hShi : S ≤ ((n : ℝ) + D) ^ (D + 1) / F`. Rewrite using `[le_div_iff₀ hF]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hy : (0 : ℝ) ≤ (n : ℝ) - D` using `sub_nonneg.mpr hnD`. Establish `hD0 : (0 : ℝ) ≤ D` using `Nat.cast_nonneg D`. Establish `hp1 : ((n : ℝ) - D) ^ (D + 1) ≤ (n : ℝ) ^ (D + 1)` using `pow_le_pow_left₀ hy (by linarith) _`. Establish `hp2 : (n : ℝ) ^ (D + 1) ≤ ((n : ℝ) + D) ^ (D + 1)` using `pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) _`. Establish `hgap` using `GridSum.pow_sub_pow_le ((n : ℝ) + D) ((n : ℝ) - D) (D + 1) hy (by linarith)`.

Rewrite `hgap` using `[Nat.add_sub_cancel]`. Establish `hpow : ((n : ℝ) + D) ^ D ≤ 2 ^ D * (n : ℝ) ^ D`. Rewrite using `[← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _`. Establish `habs : |S - (n : ℝ) ^ (D + 1) / F| ≤ ((((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1))) / F`. Rewrite using `[abs_le, sub_div]`.

Prove the components needed by the constructor for the conclusion. Establish `: ((n : ℝ) - D) ^ (D + 1) / F ≤ (n : ℝ) ^ (D + 1) / F` using `div_le_div_of_nonneg_right hp1 hF.le`. Establish `: (n : ℝ) ^ (D + 1) / F ≤ ((n : ℝ) + D) ^ (D + 1) / F` using `div_le_div_of_nonneg_right hp2 hF.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: ((n : ℝ) - D) ^ (D + 1) / F ≤ (n : ℝ) ^ (D + 1) / F` using `div_le_div_of_nonneg_right hp1 hF.le`.

Establish `: (n : ℝ) ^ (D + 1) / F ≤ ((n : ℝ) + D) ^ (D + 1) / F` using `div_le_div_of_nonneg_right hp2 hF.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnum : 0 ≤ ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1)` using `by linarith`. Establish `hdiv : ((((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1))) / F ≤ ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1)` using `div_le_self hnum hF1`. Rewrite using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ D)]`.

Establish `hk : (0 : ℝ) ≤ ((D + 1 : ℕ) : ℝ) * (2 * D)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem GridSum.proof : GridSum.Statement := by
  intro D i hi
  set j := D - i with hj
  have hD : i + j + 1 = D + 1 := by omega
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hF1 : (1 : ℝ) ≤ F := by
    rw [hFdef]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF : 0 < F := lt_of_lt_of_le one_pos hF1
  have lower : ∀ n : ℕ, ((n.choose (D + 1) : ℕ) : ℝ) ≤ ∑ a ∈ range n,
      (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) := by
    intro n
    have h := GridSum.choose_range n i j
    rw [hD] at h
    rw [← h, Nat.cast_sum]
    apply sum_le_sum
    intro a _
    rw [mul_div_mul_comm, Nat.cast_mul]
    exact mul_le_mul (GridSum.choose_le_pow_div_factorial _ _)
      (GridSum.choose_le_pow_div_factorial _ _) (by positivity) (by positivity)
  have upper : ∀ n : ℕ, ∑ a ∈ range n,
      (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) ≤
        (((n + D).choose (D + 1) : ℕ) : ℝ) := by
    intro n
    have h := GridSum.choose_range (n + D) i j
    rw [hD] at h
    rw [← h, Nat.cast_sum]
    calc ∑ a ∈ range n,
          (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ))
        ≤ ∑ a ∈ range n, (((a + i).choose i * (n + D - 1 - (a + i)).choose j : ℕ) : ℝ) := by
          apply sum_le_sum
          intro a ha
          have hb : n + D - 1 - (a + i) = (n - 1 - a) + j := by
            have := mem_range.mp ha; omega
          rw [hb, mul_div_mul_comm, Nat.cast_mul]
          exact mul_le_mul (GridSum.pow_div_factorial_le _ _)
            (GridSum.pow_div_factorial_le _ _) (by positivity) (by positivity)
      _ = ∑ a ∈ (range n).map (addRightEmbedding i),
            ((a.choose i * (n + D - 1 - a).choose j : ℕ) : ℝ) := by
          rw [sum_map]; rfl
      _ ≤ ∑ a ∈ range (n + D), ((a.choose i * (n + D - 1 - a).choose j : ℕ) : ℝ) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro x hx
            rw [Finset.mem_map] at hx
            obtain ⟨a, ha, rfl⟩ := hx
            rw [mem_range] at ha ⊢
            change a + i < n + D
            omega
          · intros; positivity
  refine IsBigO.of_bound (((D + 1 : ℕ) : ℝ) * (2 * D) * 2 ^ D) ?_
  filter_upwards [eventually_ge_atTop D] with n hn
  have hL := lower n
  have hU := upper n
  set S := ∑ a ∈ range n,
      (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ j / ((i.factorial : ℝ) * (j.factorial : ℝ)) with hS
  have hnD : (D : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : ((n : ℝ) - D) ^ (D + 1) ≤ ((n.choose (D + 1) : ℕ) : ℝ) * F := by
    have h : (n - D) ^ (D + 1) ≤ n.choose (D + 1) * (D + 1).factorial := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      have := Nat.pow_sub_le_descFactorial n (D + 1)
      rwa [show n + 1 - (D + 1) = n - D by omega] at this
    have h' : (((n - D : ℕ) : ℝ)) ^ (D + 1) ≤ ((n.choose (D + 1) : ℕ) : ℝ) * F := by
      rw [hFdef]; exact_mod_cast h
    rwa [Nat.cast_sub hn] at h'
  have h2 : (((n + D).choose (D + 1) : ℕ) : ℝ) * F ≤ ((n : ℝ) + D) ^ (D + 1) := by
    have h : (n + D).choose (D + 1) * (D + 1).factorial ≤ (n + D) ^ (D + 1) := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow _ _
    rw [hFdef]; exact_mod_cast h
  have hSlo : ((n : ℝ) - D) ^ (D + 1) / F ≤ S := by
    rw [div_le_iff₀ hF]; nlinarith
  have hShi : S ≤ ((n : ℝ) + D) ^ (D + 1) / F := by
    rw [le_div_iff₀ hF]; nlinarith
  have hy : (0 : ℝ) ≤ (n : ℝ) - D := sub_nonneg.mpr hnD
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hp1 : ((n : ℝ) - D) ^ (D + 1) ≤ (n : ℝ) ^ (D + 1) :=
    pow_le_pow_left₀ hy (by linarith) _
  have hp2 : (n : ℝ) ^ (D + 1) ≤ ((n : ℝ) + D) ^ (D + 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) _
  have hgap := GridSum.pow_sub_pow_le ((n : ℝ) + D) ((n : ℝ) - D) (D + 1) hy (by linarith)
  rw [Nat.add_sub_cancel] at hgap
  have hpow : ((n : ℝ) + D) ^ D ≤ 2 ^ D * (n : ℝ) ^ D := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have habs : |S - (n : ℝ) ^ (D + 1) / F| ≤
      ((((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1))) / F := by
    rw [abs_le, sub_div]
    constructor
    · have : ((n : ℝ) - D) ^ (D + 1) / F ≤ (n : ℝ) ^ (D + 1) / F := div_le_div_of_nonneg_right hp1 hF.le
      have : (n : ℝ) ^ (D + 1) / F ≤ ((n : ℝ) + D) ^ (D + 1) / F := div_le_div_of_nonneg_right hp2 hF.le
      linarith
    · have : ((n : ℝ) - D) ^ (D + 1) / F ≤ (n : ℝ) ^ (D + 1) / F := div_le_div_of_nonneg_right hp1 hF.le
      have : (n : ℝ) ^ (D + 1) / F ≤ ((n : ℝ) + D) ^ (D + 1) / F := div_le_div_of_nonneg_right hp2 hF.le
      linarith
  have hnum : 0 ≤ ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1) := by linarith
  have hdiv : ((((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1))) / F ≤
      ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1) := div_le_self hnum hF1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ D)]
  have hk : (0 : ℝ) ≤ ((D + 1 : ℕ) : ℝ) * (2 * D) := by positivity
  calc |S - (n : ℝ) ^ (D + 1) / F|
      ≤ ((n : ℝ) + D) ^ (D + 1) - ((n : ℝ) - D) ^ (D + 1) := habs.trans hdiv
    _ ≤ ((D + 1 : ℕ) : ℝ) * ((n + D) - (n - D)) * ((n : ℝ) + D) ^ D := hgap
    _ = ((D + 1 : ℕ) : ℝ) * (2 * D) * ((n : ℝ) + D) ^ D := by ring
    _ ≤ ((D + 1 : ℕ) : ℝ) * (2 * D) * (2 ^ D * (n : ℝ) ^ D) := mul_le_mul_of_nonneg_left hpow hk
    _ = ((D + 1 : ℕ) : ℝ) * (2 * D) * 2 ^ D * (n : ℝ) ^ D := by ring

end GroundTheory.Heights₂.Heights.HilbertSamuel
