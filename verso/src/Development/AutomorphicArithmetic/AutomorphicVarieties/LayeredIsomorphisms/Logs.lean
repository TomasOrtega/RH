import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.SecondBound

open NumberField Formalism.GaloisCohomology UpperTheory.Top UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Win

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `l J Ct X x hl hJ hCt hX hx`. Establish `hX0 : 0 < X` using `by linarith`. Establish `hx1 : 1 ≤ x` using `le_trans (Real.one_le_rpow hX (by positivity)) hx`. Establish `hlogx : 0 ≤ Real.log x` using `Real.log_nonneg hx1`.

Establish `hlogX : Real.log X ≤ J * Real.log x`. Establish `h1 : Real.log (X ^ (1 / J)) ≤ Real.log x` using `Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hx`. Rewrite `h1` using `[Real.log_rpow hX0]`. Establish `h2 : J * ((1 / J) * Real.log X) = Real.log X` using `by field_simp`. Combine the equalities or inequalities in the displayed calculation.

Establish `hl2 : (1:ℝ) / 2 < Real.log l`. Establish `h3 : Real.log 2 ≤ Real.log l` using `Real.log_le_log (by norm_num) (by exact_mod_cast hl)`. Establish `h4` using `Real.log_two_gt_d9`. Combine the linear equalities and inequalities to obtain the conclusion. Break down `Nat.eq_zero_or_pos ⌊X ^ Ct⌋₊ with h0 | hpos` into its components or cases.

Rewrite using `[h0, Nat.log_zero_right, Nat.cast_zero]`. Conclude with `mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCt) hJ.le) hlogx`. Establish `hpow : (l:ℝ) ^ (Nat.log l ⌊X ^ Ct⌋₊) ≤ X ^ Ct`. Establish `h1 : l ^ (Nat.log l ⌊X ^ Ct⌋₊) ≤ ⌊X ^ Ct⌋₊` using `Nat.pow_log_le_self l hpos.ne'`. Establish `h2 : ((⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤ X ^ Ct` using `Nat.floor_le (Real.rpow_nonneg hX0.le _)`.

Combine the equalities or inequalities in the displayed calculation. Establish `hl0 : (0:ℝ) < l` using `by exact_mod_cast (by omega : 0 < l)`. Establish `hlog` using `Real.log_le_log (pow_pos hl0 _) hpow`. Rewrite `hlog` using `[Real.log_pow, Real.log_rpow hX0]`. Establish `hk0 : (0:ℝ) ≤ (Nat.log l ⌊X ^ Ct⌋₊ : ℕ)` using `Nat.cast_nonneg _`.

Establish `hk : ((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤ 2 * (((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) * Real.log l)`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hl2.le hk0]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hlogX hCt]`. Introduce `J eps X x hJ heps hX hx`. Establish `hX0 : 0 ≤ X` using `by linarith`.

Establish `h1 : X ^ (eps / (4 * J)) = (X ^ (1 / J)) ^ (eps / 4)`. Rewrite using `[← Real.rpow_mul hX0]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h1]`.

Conclude with `Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) hx (by positivity)`. Introduce `e A1 x hx h`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hlogx : 0 ≤ Real.log x` using `Real.log_nonneg hx`. Establish `hlog` using `Real.log_le_log (by positivity) h`.

Rewrite `hlog` using `[Real.log_pow, Real.log_rpow hx0]`. Establish `h2` using `Real.log_two_gt_d9`. Establish `habs : A1 * Real.log x ≤ |A1| * Real.log x` using `mul_le_mul_of_nonneg_right (le_abs_self A1) hlogx`. Establish `he0 : (0:ℝ) ≤ e` using `Nat.cast_nonneg e`. Establish `he : (e:ℝ) ≤ 2 * (e * Real.log 2)` using `by nlinarith`.

Use polynomial arithmetic with `[abs_nonneg A1, mul_nonneg (abs_nonneg A1) hlogx]`.
-/
theorem UpperTheory.V.Win.logs :
    (∀ (l : ℕ) (J Ct X x : ℝ), 2 ≤ l → 0 < J → 0 ≤ Ct → 1 ≤ X → X ^ (1 / J) ≤ x →
        ((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤ 2 * Ct * J * Real.log x) ∧
      (∀ (J eps X x : ℝ), 0 < J → 0 < eps → 1 ≤ X → X ^ (1 / J) ≤ x → X ^ (eps / (4 * J)) ≤ x ^ (eps / 4)) ∧
      (∀ (e : ℕ) (A1 x : ℝ), 1 ≤ x → (2 : ℝ) ^ e ≤ x ^ A1 → (e : ℝ) + 2 ≤ (2 * |A1| + 2) * (1 + Real.log x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l J Ct X x hl hJ hCt hX hx
    have hX0 : 0 < X := by linarith
    have hx1 : 1 ≤ x := le_trans (Real.one_le_rpow hX (by positivity)) hx
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hlogX : Real.log X ≤ J * Real.log x := by
      have h1 : Real.log (X ^ (1 / J)) ≤ Real.log x :=
        Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hx
      rw [Real.log_rpow hX0] at h1
      have h2 : J * ((1 / J) * Real.log X) = Real.log X := by field_simp
      calc Real.log X = J * ((1 / J) * Real.log X) := h2.symm
        _ ≤ J * Real.log x := mul_le_mul_of_nonneg_left h1 hJ.le
    have hl2 : (1:ℝ) / 2 < Real.log l := by
      have h3 : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) (by exact_mod_cast hl)
      have h4 := Real.log_two_gt_d9
      linarith
    rcases Nat.eq_zero_or_pos ⌊X ^ Ct⌋₊ with h0 | hpos
    · rw [h0, Nat.log_zero_right, Nat.cast_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCt) hJ.le) hlogx
    · have hpow : (l:ℝ) ^ (Nat.log l ⌊X ^ Ct⌋₊) ≤ X ^ Ct := by
        have h1 : l ^ (Nat.log l ⌊X ^ Ct⌋₊) ≤ ⌊X ^ Ct⌋₊ := Nat.pow_log_le_self l hpos.ne'
        have h2 : ((⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤ X ^ Ct := Nat.floor_le (Real.rpow_nonneg hX0.le _)
        calc (l:ℝ) ^ (Nat.log l ⌊X ^ Ct⌋₊) = ((l ^ (Nat.log l ⌊X ^ Ct⌋₊) : ℕ) : ℝ) :=
              (Nat.cast_pow l _).symm
          _ ≤ ((⌊X ^ Ct⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
          _ ≤ X ^ Ct := h2
      have hl0 : (0:ℝ) < l := by exact_mod_cast (by omega : 0 < l)
      have hlog := Real.log_le_log (pow_pos hl0 _) hpow
      rw [Real.log_pow, Real.log_rpow hX0] at hlog
      have hk0 : (0:ℝ) ≤ (Nat.log l ⌊X ^ Ct⌋₊ : ℕ) := Nat.cast_nonneg _
      have hk : ((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤ 2 * (((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) * Real.log l) := by
        nlinarith [mul_le_mul_of_nonneg_left hl2.le hk0]
      nlinarith [mul_le_mul_of_nonneg_left hlogX hCt]
  · intro J eps X x hJ heps hX hx
    have hX0 : 0 ≤ X := by linarith
    have h1 : X ^ (eps / (4 * J)) = (X ^ (1 / J)) ^ (eps / 4) := by
      rw [← Real.rpow_mul hX0]
      congr 1
      field_simp
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) hx (by positivity)
  · intro e A1 x hx h
    have hx0 : 0 < x := by linarith
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
    have hlog := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_rpow hx0] at hlog
    have h2 := Real.log_two_gt_d9
    have habs : A1 * Real.log x ≤ |A1| * Real.log x :=
      mul_le_mul_of_nonneg_right (le_abs_self A1) hlogx
    have he0 : (0:ℝ) ≤ e := Nat.cast_nonneg e
    have he : (e:ℝ) ≤ 2 * (e * Real.log 2) := by nlinarith
    nlinarith [abs_nonneg A1, mul_nonneg (abs_nonneg A1) hlogx]
