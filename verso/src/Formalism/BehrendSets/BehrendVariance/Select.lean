import Mathlib
import Formalism.BehrendSets.Statement

open Finset

noncomputable section

namespace Formalism.BehrendSets.Select

variable {α : Type} [DecidableEq α]

/- English proof (translation)
The claim follows from `mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)`.
-/
lemma wt_nonneg (X : Finset α) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (T : Finset α) :
    0 ≤ wt X δ T :=
  mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

/- English proof (translation)
Rewrite using `[Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `T hT`. Establish `haT : a ∉ T` using `fun h => ha (Finset.mem_powerset.1 hT h)`. Establish `haXT : a ∉ X \ T` using `fun h => ha (Finset.mem_sdiff.1 h).1`.

Establish `e1 : wt (insert a X) δ T = wt X δ T * (1 - δ)`. Unfold `wt`. Rewrite using `[Finset.insert_sdiff_of_notMem X haT, Finset.card_insert_of_notMem haXT, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : wt (insert a X) δ (insert a T) = wt X δ T * δ`.

Unfold `wt`. Rewrite using `[Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem ha, Finset.card_insert_of_notMem haT, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma step (X : Finset α) (δ : ℝ) {a : α} (ha : a ∉ X) (g : Finset α → ℝ) :
    ∑ T ∈ (insert a X).powerset, wt (insert a X) δ T * g T =
      ∑ T ∈ X.powerset, wt X δ T * ((1 - δ) * g T + δ * g (insert a T)) := by
  rw [Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  have haT : a ∉ T := fun h => ha (Finset.mem_powerset.1 hT h)
  have haXT : a ∉ X \ T := fun h => ha (Finset.mem_sdiff.1 h).1
  have e1 : wt (insert a X) δ T = wt X δ T * (1 - δ) := by
    unfold wt
    rw [Finset.insert_sdiff_of_notMem X haT, Finset.card_insert_of_notMem haXT, pow_succ]
    ring
  have e2 : wt (insert a X) δ (insert a T) = wt X δ T * δ := by
    unfold wt
    rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem ha,
      Finset.card_insert_of_notMem haT, pow_succ]
    ring
  rw [e1, e2]
  ring

/- English proof (translation)
Proceed by induction on `X using Finset.induction_on with`. Consider the case `empty => simp [wt]`. Consider the case `insert a X ha ih`. Take `⟨h0, h1, h2⟩` from `ih`. Rewrite using `[step X δ ha, step X δ ha, step X δ ha, Finset.card_insert_of_notMem ha]`.

Establish `e0 : ∑ T ∈ X.powerset, wt X δ T * ((1 - δ) * 1 + δ * 1) = ∑ T ∈ X.powerset, wt X δ T * 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `T _`. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : ∑ T ∈ X.powerset, wt X δ T * ((1 - δ) * ((T.card : ℕ) : ℝ) + δ * (((insert a T).card : ℕ) : ℝ)) = ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) + δ * ∑ T ∈ X.powerset, wt X δ T * 1`.

Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `T hT`. Establish `haT : a ∉ T` using `fun h => ha (Finset.mem_powerset.1 hT h)`. Rewrite using `[Finset.card_insert_of_notMem haT]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∑ T ∈ X.powerset, wt X δ T * ((1 - δ) * ((T.card : ℕ) : ℝ) ^ 2 + δ * (((insert a T).card : ℕ) : ℝ) ^ 2) = ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) ^ 2 + 2 * δ * ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) + δ * ∑ T ∈ X.powerset, wt X δ T * 1`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `T hT`. Establish `haT : a ∉ T` using `fun h => ha (Finset.mem_powerset.1 hT h)`. Rewrite using `[Finset.card_insert_of_notMem haT]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e0, h0]`. Rewrite using `[e1, h0, h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e2, h0, h1, h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma moments (X : Finset α) (δ : ℝ) :
    (∑ T ∈ X.powerset, wt X δ T * 1 = 1) ∧
    (∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) = δ * X.card) ∧
    (∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) ^ 2 =
      δ * X.card * (1 - δ) + δ ^ 2 * (X.card : ℝ) ^ 2) := by
  induction X using Finset.induction_on with
  | empty => simp [wt]
  | insert a X ha ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    rw [step X δ ha, step X δ ha, step X δ ha, Finset.card_insert_of_notMem ha]
    have e0 : ∑ T ∈ X.powerset, wt X δ T * ((1 - δ) * 1 + δ * 1) =
        ∑ T ∈ X.powerset, wt X δ T * 1 := by
      apply Finset.sum_congr rfl
      intro T _
      ring
    have e1 : ∑ T ∈ X.powerset, wt X δ T *
          ((1 - δ) * ((T.card : ℕ) : ℝ) + δ * (((insert a T).card : ℕ) : ℝ)) =
        ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) + δ * ∑ T ∈ X.powerset, wt X δ T * 1 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      have haT : a ∉ T := fun h => ha (Finset.mem_powerset.1 hT h)
      rw [Finset.card_insert_of_notMem haT]
      push_cast
      ring
    have e2 : ∑ T ∈ X.powerset, wt X δ T *
          ((1 - δ) * ((T.card : ℕ) : ℝ) ^ 2 + δ * (((insert a T).card : ℕ) : ℝ) ^ 2) =
        ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) ^ 2
          + 2 * δ * ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ)
          + δ * ∑ T ∈ X.powerset, wt X δ T * 1 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      have haT : a ∉ T := fun h => ha (Finset.mem_powerset.1 hT h)
      rw [Finset.card_insert_of_notMem haT]
      push_cast
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [e0, h0]
    · rw [e1, h0, h1]
      push_cast
      ring
    · rw [e2, h0, h1, h2]
      push_cast
      ring

/- English proof (translation)
Take `⟨h0, h1, h2⟩` from `moments X δ`. Establish `e : ∑ T ∈ X.powerset, wt X δ T * ((T.card : ℝ) - δ * X.card) ^ 2 = ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) ^ 2 - 2 * (δ * X.card) * ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) + (δ * X.card) ^ 2 * ∑ T ∈ X.powerset, wt X δ T * 1`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `T _`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, h0, h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma variance (X : Finset α) (δ : ℝ) :
    ∑ T ∈ X.powerset, wt X δ T * ((T.card : ℝ) - δ * X.card) ^ 2 = δ * X.card * (1 - δ) := by
  obtain ⟨h0, h1, h2⟩ := moments X δ
  have e : ∑ T ∈ X.powerset, wt X δ T * ((T.card : ℝ) - δ * X.card) ^ 2 =
      ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) ^ 2
        - 2 * (δ * X.card) * ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ)
        + (δ * X.card) ^ 2 * ∑ T ∈ X.powerset, wt X δ T * 1 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T _
    ring
  rw [e, h0, h1, h2]
  ring

end Formalism.BehrendSets.Select

namespace Formalism.BehrendSets

open Formalism.BehrendSets.Select in
/- English proof (translation)
Introduce `α _ X δ lam Y hδ0 hδ1 hY hlam hvar`. Take `⟨h0, -, -⟩` from `moments X δ`. Establish `wnn : ∀ T, 0 ≤ wt X δ T` using `wt_nonneg X hδ0 hδ1`. Use `set E := expect X δ Y with hEdef`. Establish `hEs : ∑ T ∈ X.powerset, wt X δ T * Y T = E` using `rfl`.

Establish `hE : 0 ≤ E` using `Finset.sum_nonneg (fun T _ => mul_nonneg (wnn T) (hY T))`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `w1 : ∑ T ∈ X.powerset, (if lam < |(T.card : ℝ) - δ * X.card| then wt X δ T else 0) < 1 / 2`. Establish `hl2 : 0 < lam ^ 2` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `T _`. Use `split_ifs with hp`. Establish `hsq : lam ^ 2 < ((T.card : ℝ) - δ * X.card) ^ 2`.

Rewrite using `[← sq_abs ((T.card : ℝ) - δ * X.card)]`. Conclude with `pow_lt_pow_left₀ hp hlam.le (by norm_num)`. Rewrite using `[mul_div_assoc]`. Establish `: 1 ≤ ((T.card : ℝ) - δ * X.card) ^ 2 / lam ^ 2`. Rewrite using `[one_le_div hl2]`.

Conclude with `hsq.le`. Use polynomial arithmetic with `[wnn T]`. Conclude with `div_nonneg (mul_nonneg (wnn T) (sq_nonneg _)) hl2.le`. Use `_ = δ * X.card * (1 - δ) / lam ^ 2 := by`. Rewrite using `[← Finset.sum_div, variance]`.

Use `_ < 1 / 2 := by`. Rewrite using `[div_lt_iff₀ hl2]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `w2 : ∑ T ∈ X.powerset, (if 2 * E < Y T then wt X δ T else 0) ≤ 1 / 2`. Break down `hE.lt_or_eq with hEpos | hE0` into its components or cases.

Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `T _`. Establish `h2E : 0 < 2 * E` using `by linarith`. Use `split_ifs with hp`.

Rewrite using `[mul_div_assoc]`. Establish `: 1 ≤ Y T / (2 * E)`. Rewrite using `[one_le_div h2E]`. Conclude with `hp.le`. Use polynomial arithmetic with `[wnn T]`.

Conclude with `div_nonneg (mul_nonneg (wnn T) (hY T)) h2E.le`. Use `_ = E / (2 * E) := by`. Rewrite using `[← Finset.sum_div, hEs]`. Use `_ = 1 / 2 := by`. Clear the denominators using the available nonvanishing facts.

Establish `hz : ∀ T ∈ X.powerset, wt X δ T * Y T = 0`. Establish `hsum : ∑ T ∈ X.powerset, wt X δ T * Y T = 0` using `hEs.trans hE0.symm`. Conclude with `(Finset.sum_eq_zero_iff_of_nonneg (fun T _ => mul_nonneg (wnn T) (hY T))).1 hsum`. Establish `: ∑ T ∈ X.powerset, (if 2 * E < Y T then wt X δ T else 0) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `T hT`. Use `split_ifs with hp`. Rewrite `hp` using `[← hE0]`. Establish `hYp : 0 < Y T` using `by linarith`. Break down `mul_eq_zero.1 (hz T hT) with h | h` into its components or cases.

Conclude with `h`. Combine the linear equalities and inequalities to obtain the conclusion. Both sides reduce to the same expression. Rewrite using `[this]`. Evaluate the numerical expressions.

Establish `cover : ∑ T ∈ X.powerset, wt X δ T * 1 ≤ ∑ T ∈ X.powerset, (if lam < |(T.card : ℝ) - δ * X.card| then wt X δ T else 0) + ∑ T ∈ X.powerset, (if 2 * E < Y T then wt X δ T else 0)`. Rewrite using `[← Finset.sum_add_distrib]`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `T hT`. Establish `hTX : T ⊆ X` using `Finset.mem_powerset.1 hT`.

Distinguish the cases in `hp : lam < |(T.card : ℝ) - δ * X.card|`. Rewrite using `[if_pos hp, mul_one] split_ifs`. Combine the linear relations using `[wnn T]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_neg hp, mul_one, zero_add]`.

Establish `hq : 2 * E < Y T` using `hcon T hTX (not_lt.1 hp)`. Rewrite using `[if_pos hq]`. Rewrite `cover` using `[h0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem select : Select := by
  intro α _ X δ lam Y hδ0 hδ1 hY hlam hvar
  classical
  obtain ⟨h0, -, -⟩ := moments X δ
  have wnn : ∀ T, 0 ≤ wt X δ T := wt_nonneg X hδ0 hδ1
  set E := expect X δ Y with hEdef
  have hEs : ∑ T ∈ X.powerset, wt X δ T * Y T = E := rfl
  have hE : 0 ≤ E := Finset.sum_nonneg (fun T _ => mul_nonneg (wnn T) (hY T))
  by_contra hcon
  push Not at hcon

  have w1 : ∑ T ∈ X.powerset,
      (if lam < |(T.card : ℝ) - δ * X.card| then wt X δ T else 0) < 1 / 2 := by
    have hl2 : 0 < lam ^ 2 := by positivity
    calc ∑ T ∈ X.powerset, (if lam < |(T.card : ℝ) - δ * X.card| then wt X δ T else 0)
        ≤ ∑ T ∈ X.powerset, wt X δ T * ((T.card : ℝ) - δ * X.card) ^ 2 / lam ^ 2 := by
          apply Finset.sum_le_sum
          intro T _
          split_ifs with hp
          · have hsq : lam ^ 2 < ((T.card : ℝ) - δ * X.card) ^ 2 := by
              rw [← sq_abs ((T.card : ℝ) - δ * X.card)]
              exact pow_lt_pow_left₀ hp hlam.le (by norm_num)
            rw [mul_div_assoc]
            have : 1 ≤ ((T.card : ℝ) - δ * X.card) ^ 2 / lam ^ 2 := by
              rw [one_le_div hl2]
              exact hsq.le
            nlinarith [wnn T]
          · exact div_nonneg (mul_nonneg (wnn T) (sq_nonneg _)) hl2.le
      _ = δ * X.card * (1 - δ) / lam ^ 2 := by
          rw [← Finset.sum_div, variance]
      _ < 1 / 2 := by
          rw [div_lt_iff₀ hl2]
          linarith

  have w2 : ∑ T ∈ X.powerset, (if 2 * E < Y T then wt X δ T else 0) ≤ 1 / 2 := by
    rcases hE.lt_or_eq with hEpos | hE0
    · calc ∑ T ∈ X.powerset, (if 2 * E < Y T then wt X δ T else 0)
          ≤ ∑ T ∈ X.powerset, wt X δ T * Y T / (2 * E) := by
            apply Finset.sum_le_sum
            intro T _
            have h2E : 0 < 2 * E := by linarith
            split_ifs with hp
            · rw [mul_div_assoc]
              have : 1 ≤ Y T / (2 * E) := by
                rw [one_le_div h2E]
                exact hp.le
              nlinarith [wnn T]
            · exact div_nonneg (mul_nonneg (wnn T) (hY T)) h2E.le
        _ = E / (2 * E) := by
            rw [← Finset.sum_div, hEs]
        _ = 1 / 2 := by
            field_simp
    · have hz : ∀ T ∈ X.powerset, wt X δ T * Y T = 0 := by
        have hsum : ∑ T ∈ X.powerset, wt X δ T * Y T = 0 := hEs.trans hE0.symm
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun T _ => mul_nonneg (wnn T) (hY T))).1 hsum
      have : ∑ T ∈ X.powerset, (if 2 * E < Y T then wt X δ T else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro T hT
        split_ifs with hp
        · rw [← hE0] at hp
          have hYp : 0 < Y T := by linarith
          rcases mul_eq_zero.1 (hz T hT) with h | h
          · exact h
          · linarith
        · rfl
      rw [this]
      norm_num

  have cover : ∑ T ∈ X.powerset, wt X δ T * 1 ≤
      ∑ T ∈ X.powerset, (if lam < |(T.card : ℝ) - δ * X.card| then wt X δ T else 0) +
      ∑ T ∈ X.powerset, (if 2 * E < Y T then wt X δ T else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro T hT
    have hTX : T ⊆ X := Finset.mem_powerset.1 hT
    by_cases hp : lam < |(T.card : ℝ) - δ * X.card|
    · rw [if_pos hp, mul_one]
      split_ifs
      · linarith [wnn T]
      · linarith
    · rw [if_neg hp, mul_one, zero_add]
      have hq : 2 * E < Y T := hcon T hTX (not_lt.1 hp)
      rw [if_pos hq]
  rw [h0] at cover
  linarith

end Formalism.BehrendSets
