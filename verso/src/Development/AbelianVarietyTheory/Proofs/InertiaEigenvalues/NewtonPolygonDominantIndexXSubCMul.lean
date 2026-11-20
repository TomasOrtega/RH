import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[mul_comm, coeff_mul_X_sub_C]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rcout_coeff_succ {K : Type} [NormedField K] (g : K[X]) (a : K) (k : ℕ) :
    ((X - C a) * g).coeff (k + 1) = g.coeff k - a * g.coeff (k + 1) := by
  rw [mul_comm, coeff_mul_X_sub_C]; ring

/- English proof (translation)
Rewrite using `[mul_coeff_zero]`. Simplify using the standard rewrite rules.
-/
theorem rcout_coeff_zero {K : Type} [NormedField K] (g : K[X]) (a : K) :
    ((X - C a) * g).coeff 0 = -(a * g.coeff 0) := by
  rw [mul_coeff_zero]; simp

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, ← norm_neg y]`. Conclude with `IsUltrametricDist.norm_add_le_max _ _`.
-/
theorem rcout_ultra {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) :
    ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

/- English proof (translation)
Introduce `K _ _ g a ρ d hρ ha hle hlt`. Use `set M := ‖g.coeff d‖ * ρ ^ d with hM`. Establish `hMpos : 0 < M`. Use `hlt (d + 1) (Nat.lt_succ_self d)` as an intermediate fact. Conclude with `lt_of_le_of_lt (by positivity) this`.

Establish `hapos : 0 < ‖a‖` using `hρ.trans ha`. Establish `hshift : ∀ k, ‖g.coeff k‖ * ρ ^ (k + 1) ≤ ρ * M`. Introduce `k`. Use `hle k` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.

Establish `hρM : ρ * M < ‖a‖ * M` using `mul_lt_mul_of_pos_right ha hMpos`. Establish `haterm : ∀ j, ‖a * g.coeff j‖ * ρ ^ j = ‖a‖ * (‖g.coeff j‖ * ρ ^ j)`. Introduce `j`. Rewrite using `[norm_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hup : ∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖a‖ * M`. Introduce `j`. Establish `hpj : 0 ≤ ρ ^ j` using `by positivity`. Consider the cases of `j with`. Consider the case `zero`.

Rewrite using `[rcout_coeff_zero, norm_neg, haterm]`. Conclude with `mul_le_mul_of_nonneg_left (hle 0) hapos.le`. Consider the case `succ k`. Rewrite using `[rcout_coeff_succ]`. Combine the equalities or inequalities in the displayed calculation.

Apply `max_le` to reduce the goal to its premises. Conclude with `(hshift k).trans hρM.le`. Rewrite using `[haterm]`. Conclude with `mul_le_mul_of_nonneg_left (hle (k + 1)) hapos.le`. Establish `hupl : ∀ j, d < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖a‖ * M`.

Introduce `j hj`. Establish `hpj : 0 ≤ ρ ^ j` using `by positivity`. Take `⟨k, rfl⟩ : ∃ k, j = k + 1` from `⟨j - 1, by omega⟩`. Rewrite using `[rcout_coeff_succ]`. Combine the equalities or inequalities in the displayed calculation.

Apply `max_lt` to reduce the goal to its premises. Conclude with `lt_of_le_of_lt (hshift k) hρM`. Rewrite using `[haterm]`. Conclude with `mul_lt_mul_of_pos_left (hlt (k + 1) hj) hapos`. Establish `hlow : ‖a‖ * M ≤ ‖((X - C a) * g).coeff d‖ * ρ ^ d`.

Establish `hpd : 0 < ρ ^ d` using `by positivity`. Consider the cases of `d with`. Consider the case `zero`. Rewrite using `[rcout_coeff_zero, norm_neg, haterm]`. Consider the case `succ k`.

Rewrite using `[rcout_coeff_succ]`. Use `set c := g.coeff k - a * g.coeff (k + 1)`. Establish `key : a * g.coeff (k + 1) = g.coeff k - c` using `by simp [c]`. Establish `h1 : ‖a‖ * M = ‖g.coeff k - c‖ * ρ ^ (k + 1)`. Rewrite using `[← key, haterm]`.

Establish `h2 : ‖g.coeff k - c‖ * ρ ^ (k + 1) ≤ max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖c‖ * ρ ^ (k + 1))`. Rewrite using `[← max_mul_of_nonneg _ _ hpd.le]`. Conclude with `mul_le_mul_of_nonneg_right (rcout_ultra _ _) hpd.le`. Break down `le_max_iff.mp (h1 ▸ h2 : ‖a‖ * M ≤ _) with h | h` into its components or cases. Conclude with `absurd (lt_of_le_of_lt ((hshift k)) hρM) (not_lt.mpr h)`.

Conclude with `h`. Conclude with `⟨fun j => (hup j).trans hlow, fun j hj => (hupl j hj).trans_le hlow⟩`.
-/
theorem newton_step_root_outside_disc :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ), 0 < ρ → ρ < ‖a‖ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) → (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) → (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff d‖ * ρ ^ d) ∧ ∀ j, d < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖((X - C a) * g).coeff d‖ * ρ ^ d := by
  intro K _ _ g a ρ d hρ ha hle hlt
  set M := ‖g.coeff d‖ * ρ ^ d with hM
  have hMpos : 0 < M := by
    have := hlt (d + 1) (Nat.lt_succ_self d)
    exact lt_of_le_of_lt (by positivity) this
  have hapos : 0 < ‖a‖ := hρ.trans ha

  have hshift : ∀ k, ‖g.coeff k‖ * ρ ^ (k + 1) ≤ ρ * M := by
    intro k
    have := hle k
    calc ‖g.coeff k‖ * ρ ^ (k + 1) = ρ * (‖g.coeff k‖ * ρ ^ k) := by ring
      _ ≤ ρ * M := mul_le_mul_of_nonneg_left this hρ.le
  have hρM : ρ * M < ‖a‖ * M := mul_lt_mul_of_pos_right ha hMpos

  have haterm : ∀ j, ‖a * g.coeff j‖ * ρ ^ j = ‖a‖ * (‖g.coeff j‖ * ρ ^ j) := by
    intro j; rw [norm_mul]; ring

  have hup : ∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖a‖ * M := by
    intro j
    have hpj : 0 ≤ ρ ^ j := by positivity
    cases j with
    | zero =>
      rw [rcout_coeff_zero, norm_neg, haterm]
      exact mul_le_mul_of_nonneg_left (hle 0) hapos.le
    | succ k =>
      rw [rcout_coeff_succ]
      calc ‖g.coeff k - a * g.coeff (k + 1)‖ * ρ ^ (k + 1)
          ≤ max ‖g.coeff k‖ ‖a * g.coeff (k + 1)‖ * ρ ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (rcout_ultra _ _) hpj
        _ = max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖a * g.coeff (k + 1)‖ * ρ ^ (k + 1)) :=
            max_mul_of_nonneg _ _ hpj
        _ ≤ ‖a‖ * M := by
            apply max_le
            · exact (hshift k).trans hρM.le
            · rw [haterm]; exact mul_le_mul_of_nonneg_left (hle (k + 1)) hapos.le

  have hupl : ∀ j, d < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖a‖ * M := by
    intro j hj
    have hpj : 0 ≤ ρ ^ j := by positivity
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [rcout_coeff_succ]
    calc ‖g.coeff k - a * g.coeff (k + 1)‖ * ρ ^ (k + 1)
        ≤ max ‖g.coeff k‖ ‖a * g.coeff (k + 1)‖ * ρ ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (rcout_ultra _ _) hpj
      _ = max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖a * g.coeff (k + 1)‖ * ρ ^ (k + 1)) :=
          max_mul_of_nonneg _ _ hpj
      _ < ‖a‖ * M := by
          apply max_lt
          · exact lt_of_le_of_lt (hshift k) hρM
          · rw [haterm]; exact mul_lt_mul_of_pos_left (hlt (k + 1) hj) hapos

  have hlow : ‖a‖ * M ≤ ‖((X - C a) * g).coeff d‖ * ρ ^ d := by
    have hpd : 0 < ρ ^ d := by positivity
    cases d with
    | zero =>
      rw [rcout_coeff_zero, norm_neg, haterm]
    | succ k =>
      rw [rcout_coeff_succ]
      set c := g.coeff k - a * g.coeff (k + 1)
      have key : a * g.coeff (k + 1) = g.coeff k - c := by simp [c]
      have h1 : ‖a‖ * M = ‖g.coeff k - c‖ * ρ ^ (k + 1) := by
        rw [← key, haterm]
      have h2 : ‖g.coeff k - c‖ * ρ ^ (k + 1) ≤
          max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖c‖ * ρ ^ (k + 1)) := by
        rw [← max_mul_of_nonneg _ _ hpd.le]
        exact mul_le_mul_of_nonneg_right (rcout_ultra _ _) hpd.le
      rcases le_max_iff.mp (h1 ▸ h2 : ‖a‖ * M ≤ _) with h | h
      · exact absurd (lt_of_le_of_lt ((hshift k)) hρM) (not_lt.mpr h)
      · exact h
  exact ⟨fun j => (hup j).trans hlow, fun j hj => (hupl j hj).trans_le hlow⟩

end GlobalTheory
