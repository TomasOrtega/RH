import Formalism.PolynomialDimension.DigitClassSize

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

/- English proof (translation)
Unfold `weylDim`. Simplify using `only [Fin.prod_univ_succ (n := m + 1)]`. Simplify using `only [Fin.prod_univ_castSucc (n := m)]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_last, lt_self_iff_false, Fin.not_lt_zero, if_false, Fin.succ_pos, if_true, Fin.succ_lt_succ_iff, Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.val_zero, one_mul …`. Establish `hl : ∀ x : Fin m, ¬ (Fin.last m < x.castSucc)` using `fun x => (Fin.castSucc_lt_last x).asymm`.

Simplify using `only [hl, if_false, Finset.prod_const_one, mul_one]`. Use `push_cast`. Simplify using `only [sub_zero, ← add_assoc, add_sub_add_right_eq_sub, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weylDim_cons_snoc (m : ℕ) (a b : ℤ) (μ : Fin m → ℤ) :
    weylDim (m + 2) (Fin.cons a (Fin.snoc μ b) : Fin (m + 2) → ℤ) =
      weylDim m μ * (∏ j : Fin m, ((((a - μ j : ℤ)) : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) *
      (∏ j : Fin m, ((((μ j - b : ℤ)) : ℚ) + (m : ℚ) - ((j : ℕ) : ℚ)) / ((m : ℚ) - ((j : ℕ) : ℚ))) *
      (((((a - b : ℤ)) : ℚ) + (m : ℚ) + 1) / ((m : ℚ) + 1)) := by
  unfold weylDim
  simp only [Fin.prod_univ_succ (n := m + 1)]
  simp only [Fin.prod_univ_castSucc (n := m)]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_last, lt_self_iff_false,
    Fin.not_lt_zero, if_false, Fin.succ_pos, if_true, Fin.succ_lt_succ_iff,
    Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
    Fin.val_zero, one_mul, mul_one]
  have hl : ∀ x : Fin m, ¬ (Fin.last m < x.castSucc) := fun x => (Fin.castSucc_lt_last x).asymm
  simp only [hl, if_false, Finset.prod_const_one, mul_one]
  push_cast
  simp only [sub_zero, ← add_assoc, add_sub_add_right_eq_sub, Finset.prod_mul_distrib]
  ring

/- English proof (translation)
Unfold `weylDim`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `i _`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `j _`.

Use `split_ifs with h`. Establish `: ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) ≠ 0`. Establish `: (i : ℕ) < (j : ℕ)` using `h`. Establish `: ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ)` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `[this]`. Both sides reduce to the same expression.
-/
theorem weylDim_zero (m : ℕ) : weylDim m (fun _ => (0 : ℤ)) = 1 := by
  unfold weylDim
  apply Finset.prod_eq_one; intro i _
  apply Finset.prod_eq_one; intro j _
  split_ifs with h
  · have : ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) ≠ 0 := by
      have : (i : ℕ) < (j : ℕ) := h
      have : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast this
      linarith
    simp [this]
  · rfl

/- English proof (translation)
Unfold `weylDim`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `i _`. Apply `Finset.prod_pos` to reduce the goal to its premises. Introduce `j _`.

Use `split_ifs with h`. Establish `h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ)` using `by exact_mod_cast (show (i : ℕ) < (j : ℕ) from h)`. Establish `h2 : μ j ≤ μ i` using `hμ h.le`. Establish `h3 : ((μ j : ℤ) : ℚ) ≤ ((μ i : ℤ) : ℚ)` using `by exact_mod_cast h2`. Use `push_cast`.

Apply the tactic sequence `apply div_pos <;> linarith`. Conclude with `one_pos`.
-/
theorem weylDim_pos_of_antitone (m : ℕ) (μ : Fin m → ℤ) (hμ : Antitone μ) : 0 < weylDim m μ := by
  unfold weylDim
  apply Finset.prod_pos; intro i _
  apply Finset.prod_pos; intro j _
  split_ifs with h
  · have h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast (show (i : ℕ) < (j : ℕ) from h)
    have h2 : μ j ≤ μ i := hμ h.le
    have h3 : ((μ j : ℤ) : ℚ) ≤ ((μ i : ℤ) : ℚ) := by exact_mod_cast h2
    push_cast
    apply div_pos <;> linarith
  · exact one_pos

/- English proof (translation)
Unfold `hwt`. Rewrite using `[weylDim_cons_snoc, weylDim_zero]`. Use `push_cast`. Simplify using `only [sub_zero, sub_neg_eq_add, one_mul, zero_add]`.
-/
theorem weylDim_hwt (m A B : ℕ) : (weylDim (m + 2) (hwt m A B) : ℝ) =
    (∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) *
    (∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) *
    (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1)) := by
  unfold hwt
  rw [weylDim_cons_snoc, weylDim_zero]
  push_cast
  simp only [sub_zero, sub_neg_eq_add, one_mul, zero_add]

/- English proof (translation)
Unfold `cwt`. Rewrite using `[weylDim_cons_snoc]`. Use `push_cast`. Simplify using `only [sub_neg_eq_add]`.
-/
theorem weylDim_cwt (m A c B : ℕ) (μ : Fin m → ℤ) : (weylDim (m + 2) (cwt m A c B μ) : ℝ) =
    (weylDim m μ : ℝ) *
    (∏ j : Fin m, ((A : ℝ) + c - (μ j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) *
    (∏ j : Fin m, ((μ j : ℝ) + B + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) *
    (((A : ℝ) + c + B + m + 1) / ((m : ℝ) + 1)) := by
  unfold cwt
  rw [weylDim_cons_snoc]
  push_cast
  simp only [sub_neg_eq_add]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem prod_le_pow_mul_prod (m : ℕ) (f g : Fin m → ℝ) (t : ℝ) (hf : ∀ j, 0 ≤ f j)
    (hfg : ∀ j, f j ≤ (1 + t) * g j) :
    ∏ j, f j ≤ (1 + t) ^ m * ∏ j, g j := by
  calc ∏ j, f j ≤ ∏ j, ((1 + t) * g j) := Finset.prod_le_prod (fun j _ => hf j) (fun j _ => hfg j)
    _ = (1 + t) ^ m * ∏ j, g j := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Establish `: ((j : ℕ) : ℝ) < (m : ℝ)` using `by exact_mod_cast j.isLt`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fin_sub_pos (m : ℕ) (j : Fin m) : 0 < (m : ℝ) - ((j : ℕ) : ℝ) := by
  have : ((j : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast j.isLt
  linarith

/- English proof (translation)
Rewrite using `[weylDim_hwt]`. Establish `h1 : 0 < ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)` using `Finset.prod_pos fun j _ => by positivity`. Establish `h2 : 0 < ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))` using `Finset.prod_pos fun j _ => by`. Use `fin_sub_pos m j` as an intermediate fact. Apply the tactic sequence `apply div_pos <;> linarith [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]`.

Establish `h3 : 0 < ((A : ℝ) + B + m + 1) / ((m : ℝ) + 1)` using `by positivity`. Check the signs of the components of the expression.
-/
theorem hwt_pos (m A B : ℕ) : 0 < (weylDim (m + 2) (hwt m A B) : ℝ) := by
  rw [weylDim_hwt]
  have h1 : 0 < ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_pos fun j _ => by positivity
  have h2 : 0 < ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_pos fun j _ => by
      have := fin_sub_pos m j
      apply div_pos <;> linarith [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  have h3 : 0 < ((A : ℝ) + B + m + 1) / ((m : ℝ) + 1) := by positivity
  positivity

/- English proof (translation)
Establish `hW : 0 < (weylDim m μ : ℝ)` using `by exact_mod_cast weylDim_pos_of_antitone m μ hμ`. Establish `hμ0 : ∀ j, (0 : ℝ) ≤ (μ j : ℝ)` using `fun j => by exact_mod_cast (h0 j).1`. Establish `hμc : ∀ j, (μ j : ℝ) ≤ (c : ℝ)` using `fun j => by exact_mod_cast (h0 j).2`. Establish `hA0 : (0 : ℝ) ≤ A` using `Nat.cast_nonneg A`. Establish `hB0 : (0 : ℝ) ≤ B` using `Nat.cast_nonneg B`.

Establish `hm0 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`. Establish `hc0 : (0 : ℝ) ≤ c` using `Nat.cast_nonneg c`. Rewrite using `[weylDim_cwt, weylDim_hwt]`. Establish `f1 : ∀ j : Fin m, 0 ≤ ((A : ℝ) + c - (μ j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)`. Introduce `j`.

Use `hμc j` as an intermediate fact. Establish `: (0 : ℝ) ≤ ((j : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Apply `div_nonneg` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Check the signs of the components of the expression.

Establish `f2 : ∀ j : Fin m, 0 ≤ ((μ j : ℝ) + B + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))`. Apply the tactic sequence `intro j; have := fin_sub_pos m j; have := hμ0 j; apply div_nonneg <;> linarith`. Establish `f3 : 0 ≤ ((A : ℝ) + c + B + m + 1) / ((m : ℝ) + 1)` using `by positivity`. Establish `P1` using `prod_le_pow_mul_prod m _ (fun j : Fin m => ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) t f1 (fun j => by`. Rewrite using `[← mul_div_assoc]`.

Apply `div_le_div_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Use `hμ0 j` as an intermediate fact. Establish `: 0 ≤ t * (((j : ℕ) : ℝ) + 1)` using `by positivity`. Use the proof step `nlinarith)`. Establish `P2` using `prod_le_pow_mul_prod m _ (fun j : Fin m => ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) t f2 (fun j => by`.

Rewrite using `[← mul_div_assoc]`. Apply `div_le_div_of_nonneg_right _ (fin_sub_pos m j).le` to reduce the goal to its premises. Use `hμc j` as an intermediate fact. Use `fin_sub_pos m j` as an intermediate fact. Establish `: 0 ≤ t * ((m : ℝ) - ((j : ℕ) : ℝ))` using `by positivity`.

Use the proof step `nlinarith)`. Establish `P3 : ((A : ℝ) + c + B + m + 1) / ((m : ℝ) + 1) ≤ (1 + t) * (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1))`. Rewrite using `[← mul_div_assoc]`. Apply `div_le_div_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Establish `: 0 ≤ t * ((B : ℝ) + m + 1)` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `g1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + c - (μ j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)` using `Finset.prod_nonneg fun j _ => f1 j`. Establish `g2 : 0 ≤ ∏ j : Fin m, ((μ j : ℝ) + B + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))` using `Finset.prod_nonneg fun j _ => f2 j`. Establish `k1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)` using `Finset.prod_nonneg fun j _ => by positivity`. Apply the tactic sequence `have k2 : 0 ≤ ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) := Finset.prod_nonneg fun j _ => by have := fin_sub_pos m j; apply div_nonneg <;> linarith`.

Establish `k3 : 0 ≤ (1 + t) ^ m` using `by positivity`. Use `⟨by positivity, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cwt_bound (m A c B : ℕ) (μ : Fin m → ℤ) (hμ : Antitone μ) (h0 : ∀ i, 0 ≤ μ i ∧ μ i ≤ c)
    (t : ℝ) (ht : 0 ≤ t) (hA : (c : ℝ) ≤ t * A) (hB : (c : ℝ) ≤ t * B) :
    0 ≤ (weylDim (m + 2) (cwt m A c B μ) : ℝ) ∧
    (weylDim (m + 2) (cwt m A c B μ) : ℝ) ≤
      (1 + t) ^ (2 * m + 1) * ((weylDim m μ : ℝ) * (weylDim (m + 2) (hwt m A B) : ℝ)) := by
  have hW : 0 < (weylDim m μ : ℝ) := by exact_mod_cast weylDim_pos_of_antitone m μ hμ
  have hμ0 : ∀ j, (0 : ℝ) ≤ (μ j : ℝ) := fun j => by exact_mod_cast (h0 j).1
  have hμc : ∀ j, (μ j : ℝ) ≤ (c : ℝ) := fun j => by exact_mod_cast (h0 j).2
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  rw [weylDim_cwt, weylDim_hwt]
  have f1 : ∀ j : Fin m, 0 ≤ ((A : ℝ) + c - (μ j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) := by
    intro j
    have := hμc j
    have : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    apply div_nonneg
    · linarith
    · positivity
  have f2 : ∀ j : Fin m, 0 ≤ ((μ j : ℝ) + B + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) := by
    intro j; have := fin_sub_pos m j; have := hμ0 j; apply div_nonneg <;> linarith
  have f3 : 0 ≤ ((A : ℝ) + c + B + m + 1) / ((m : ℝ) + 1) := by positivity
  have P1 := prod_le_pow_mul_prod m _ (fun j : Fin m => ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) t f1
    (fun j => by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := hμ0 j
      have : 0 ≤ t * (((j : ℕ) : ℝ) + 1) := by positivity
      nlinarith)
  have P2 := prod_le_pow_mul_prod m _ (fun j : Fin m => ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) t f2
    (fun j => by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (fin_sub_pos m j).le
      have := hμc j
      have := fin_sub_pos m j
      have : 0 ≤ t * ((m : ℝ) - ((j : ℕ) : ℝ)) := by positivity
      nlinarith)
  have P3 : ((A : ℝ) + c + B + m + 1) / ((m : ℝ) + 1) ≤ (1 + t) * (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1)) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 ≤ t * ((B : ℝ) + m + 1) := by positivity
    nlinarith
  have g1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + c - (μ j : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_nonneg fun j _ => f1 j
  have g2 : 0 ≤ ∏ j : Fin m, ((μ j : ℝ) + B + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun j _ => f2 j
  have k1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_nonneg fun j _ => by positivity
  have k2 : 0 ≤ ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun j _ => by have := fin_sub_pos m j; apply div_nonneg <;> linarith
  have k3 : 0 ≤ (1 + t) ^ m := by positivity
  refine ⟨by positivity, ?_⟩
  calc _ ≤ (weylDim m μ : ℝ) *
        ((1 + t) ^ m * ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) *
        ((1 + t) ^ m * ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) *
        ((1 + t) * (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1))) := by gcongr
    _ = _ := by ring

/- English proof (translation)
Establish `hA0 : (0 : ℝ) ≤ A` using `Nat.cast_nonneg A`. Establish `hB0 : (0 : ℝ) ≤ B` using `Nat.cast_nonneg B`. Establish `hm0 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`. Establish `hc0 : (0 : ℝ) ≤ c` using `Nat.cast_nonneg c`. Rewrite using `[weylDim_hwt, weylDim_hwt]`.

Use `push_cast`. Establish `f1 : ∀ j : Fin m, 0 ≤ ((A : ℝ) + c + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)` using `fun j => by positivity`. Establish `f2 : ∀ j : Fin m, 0 ≤ ((B : ℝ) + c + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))`. Apply the tactic sequence `intro j; have := fin_sub_pos m j; apply div_nonneg <;> linarith`. Establish `P1` using `prod_le_pow_mul_prod m _ (fun j : Fin m => ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) t f1 (fun j => by`.

Rewrite using `[← mul_div_assoc]`. Apply `div_le_div_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Establish `: 0 ≤ t * (((j : ℕ) : ℝ) + 1)` using `by positivity`. Use the proof step `nlinarith)`. Establish `P2` using `prod_le_pow_mul_prod m _ (fun j : Fin m => ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) t f2 (fun j => by`.

Rewrite using `[← mul_div_assoc]`. Apply `div_le_div_of_nonneg_right _ (fin_sub_pos m j).le` to reduce the goal to its premises. Use `fin_sub_pos m j` as an intermediate fact. Establish `: 0 ≤ t * ((m : ℝ) - ((j : ℕ) : ℝ))` using `by positivity`. Use the proof step `nlinarith)`.

Establish `P3 : ((A : ℝ) + c + (B + c) + m + 1) / ((m : ℝ) + 1) ≤ (1 + t) * (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1))`. Rewrite using `[← mul_div_assoc]`. Apply `div_le_div_of_nonneg_right _ (by positivity)` to reduce the goal to its premises. Establish `: 0 ≤ t * ((m : ℝ) + 1)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Establish `g1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + c + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)` using `Finset.prod_nonneg fun j _ => f1 j`. Establish `g2 : 0 ≤ ∏ j : Fin m, ((B : ℝ) + c + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))` using `Finset.prod_nonneg fun j _ => f2 j`. Establish `f3 : 0 ≤ ((A : ℝ) + c + (B + c) + m + 1) / ((m : ℝ) + 1)` using `by positivity`. Establish `k1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)` using `Finset.prod_nonneg fun j _ => by positivity`. Apply the tactic sequence `have k2 : 0 ≤ ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) := Finset.prod_nonneg fun j _ => by have := fin_sub_pos m j; apply div_nonneg <;> linarith`.

Establish `k3 : 0 ≤ (1 + t) ^ m` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hwt_bound (m A c B : ℕ) (t : ℝ) (ht : 0 ≤ t) (hA : (c : ℝ) ≤ t * A) (hB : (c : ℝ) ≤ t * B) :
    (weylDim (m + 2) (hwt m (A + c) (B + c)) : ℝ) ≤ (1 + t) ^ (2 * m + 1) * (weylDim (m + 2) (hwt m A B) : ℝ) := by
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  rw [weylDim_hwt, weylDim_hwt]
  push_cast
  have f1 : ∀ j : Fin m, 0 ≤ ((A : ℝ) + c + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) := fun j => by positivity
  have f2 : ∀ j : Fin m, 0 ≤ ((B : ℝ) + c + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) := by
    intro j; have := fin_sub_pos m j; apply div_nonneg <;> linarith
  have P1 := prod_le_pow_mul_prod m _ (fun j : Fin m => ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) t f1
    (fun j => by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ t * (((j : ℕ) : ℝ) + 1) := by positivity
      nlinarith)
  have P2 := prod_le_pow_mul_prod m _ (fun j : Fin m => ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) t f2
    (fun j => by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (fin_sub_pos m j).le
      have := fin_sub_pos m j
      have : 0 ≤ t * ((m : ℝ) - ((j : ℕ) : ℝ)) := by positivity
      nlinarith)
  have P3 : ((A : ℝ) + c + (B + c) + m + 1) / ((m : ℝ) + 1) ≤ (1 + t) * (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1)) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 ≤ t * ((m : ℝ) + 1) := by positivity
    nlinarith
  have g1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + c + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_nonneg fun j _ => f1 j
  have g2 : 0 ≤ ∏ j : Fin m, ((B : ℝ) + c + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun j _ => f2 j
  have f3 : 0 ≤ ((A : ℝ) + c + (B + c) + m + 1) / ((m : ℝ) + 1) := by positivity
  have k1 : 0 ≤ ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1) :=
    Finset.prod_nonneg fun j _ => by positivity
  have k2 : 0 ≤ ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun j _ => by have := fin_sub_pos m j; apply div_nonneg <;> linarith
  have k3 : 0 ≤ (1 + t) ^ m := by positivity
  calc _ ≤ ((1 + t) ^ m * ∏ j : Fin m, ((A : ℝ) + ((j : ℕ) : ℝ) + 1) / (((j : ℕ) : ℝ) + 1)) *
        ((1 + t) ^ m * ∏ j : Fin m, ((B : ℝ) + (m : ℝ) - ((j : ℕ) : ℝ)) / ((m : ℝ) - ((j : ℕ) : ℝ))) *
        ((1 + t) * (((A : ℝ) + B + m + 1) / ((m : ℝ) + 1))) := by gcongr
    _ = _ := by ring

/- English proof (translation)
Use `⟨8 * Real.exp 8, by positivity, ?_⟩` and prove the remaining obligations. Introduce `N m c A B cl b' hanti hcl hb hAB hsize`. Establish `hc0 : (0 : ℝ) ≤ c` using `Nat.cast_nonneg c`. Establish `hN0 : (0 : ℝ) ≤ N` using `Nat.cast_nonneg N`. Establish `hm0 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`.

Use `set t : ℝ := 4 * c / b' with ht_def`. Establish `ht : 0 ≤ t` using `by positivity`. Establish `hA : ∀ s, (c : ℝ) ≤ t * A s` using `fun s => by`. Rewrite using `[ht_def, div_mul_eq_mul_div, le_div_iff₀ hb]`. Use `(hAB s).1` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `hB : ∀ s, (c : ℝ) ≤ t * B s` using `fun s => by`. Rewrite using `[ht_def, div_mul_eq_mul_div, le_div_iff₀ hb]`. Use `(hAB s).2` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Use `set x : ℝ := N * (m + 2) * c / b' with hx_def`. Establish `hx0 : 0 ≤ x` using `by positivity`. Establish `hx1 : x ≤ 1` using `by rw [hx_def, div_le_one hb]; exact hsize`. Establish `hCx : 8 * Real.exp 8 * N * (m + 2) * c / b' = 8 * Real.exp 8 * x`. Rewrite using `[hx_def]`.

Expand and normalize the polynomial expressions, which then agree. Use `set K : ℕ := (2 * m + 1) * N with hK`. Establish `hKt : (K : ℝ) * t ≤ 8 * x`. Establish `e1 : (K : ℝ) * t = (4 * ((2 * m + 1) * N * c)) / b'`. Rewrite using `[hK, ht_def]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : 8 * x = (8 * (N * (m + 2) * c)) / b'` using `by rw [hx_def]; ring`. Rewrite using `[e1, e2]`. Apply `div_le_div_of_nonneg_right _ hb.le` to reduce the goal to its premises.

Establish `: 0 ≤ (N : ℝ) * c` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hE : (1 + t) ^ K ≤ Real.exp (8 * x)`. Combine the equalities or inequalities in the displayed calculation. Establish `hexp1 : (1 - 8 * x) * Real.exp (8 * x) ≤ 1`.

Establish `h1` using `Real.add_one_le_exp (-(8 * x))`. Establish `h2` using `Real.exp_pos (8 * x)`. Combine the equalities or inequalities in the displayed calculation. Establish `hexp8 : 1 ≤ Real.exp 8` using `Real.one_le_exp (by norm_num)`. Establish `hct` using `fun s => cwt_bound m (A s) c (B s) (cl s) (hanti s) (hcl s) t ht (hA s) (hB s)`.

Establish `hPl : 0 < ∏ s, (weylDim m (cl s) : ℝ)` using `Finset.prod_pos fun s _ => by exact_mod_cast weylDim_pos_of_antitone m (cl s) (hanti s)`. Establish `hPh : 0 < ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ)` using `Finset.prod_pos fun s _ => hwt_pos m (A s) (B s)`. Establish `hPc0 : 0 ≤ ∏ s, (weylDim (m + 2) (cwt m (A s) c (B s) (cl s)) : ℝ)` using `Finset.prod_nonneg fun s _ => (hct s).1`. Establish `Pc : ∏ s, (weylDim (m + 2) (cwt m (A s) c (B s) (cl s)) : ℝ) ≤ (1 + t) ^ K * ((∏ s, (weylDim m (cl s) : ℝ)) * ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]`. Establish `Ph : ∏ s, (weylDim (m + 2) (hwt m (A s + c) (B s + c)) : ℝ) ≤ (1 + t) ^ K * ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]`. Rewrite using `[hCx]`.

Simplify using `only [Rat.cast_prod, Rat.cast_mul]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `set Q := (∏ s, (weylDim m (cl s) : ℝ)) * ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ)`. Establish `hQ : 0 ≤ Q` using `by positivity`. Distinguish the cases in `h : 1 - 8 * Real.exp 8 * x ≤ 0`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `h` using `[not_le]`. Establish `hC : 8 * x ≤ 8 * Real.exp 8 * x` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hy : Real.exp (8 * x) ≤ 1 + 8 * Real.exp 8 * x`.

Establish `h8 : Real.exp (8 * x) ≤ Real.exp 8` using `Real.exp_le_exp.mpr (by linarith)`. Establish `: 8 * x * Real.exp (8 * x) ≤ 8 * x * Real.exp 8` using `mul_le_mul_of_nonneg_left h8 (by positivity)`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cloud_dimensions_bound : CloudDims := by
  refine ⟨8 * Real.exp 8, by positivity, ?_⟩
  intro N m c A B cl b' hanti hcl hb hAB hsize
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set t : ℝ := 4 * c / b' with ht_def
  have ht : 0 ≤ t := by positivity
  have hA : ∀ s, (c : ℝ) ≤ t * A s := fun s => by
    rw [ht_def, div_mul_eq_mul_div, le_div_iff₀ hb]
    have := (hAB s).1
    nlinarith
  have hB : ∀ s, (c : ℝ) ≤ t * B s := fun s => by
    rw [ht_def, div_mul_eq_mul_div, le_div_iff₀ hb]
    have := (hAB s).2
    nlinarith
  set x : ℝ := N * (m + 2) * c / b' with hx_def
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hx_def, div_le_one hb]; exact hsize
  have hCx : 8 * Real.exp 8 * N * (m + 2) * c / b' = 8 * Real.exp 8 * x := by
    rw [hx_def]; ring
  set K : ℕ := (2 * m + 1) * N with hK
  have hKt : (K : ℝ) * t ≤ 8 * x := by
    have e1 : (K : ℝ) * t = (4 * ((2 * m + 1) * N * c)) / b' := by
      rw [hK, ht_def]; push_cast; ring
    have e2 : 8 * x = (8 * (N * (m + 2) * c)) / b' := by rw [hx_def]; ring
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ hb.le
    have : 0 ≤ (N : ℝ) * c := by positivity
    nlinarith
  have hE : (1 + t) ^ K ≤ Real.exp (8 * x) := by
    calc (1 + t) ^ K ≤ (Real.exp t) ^ K :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp t]) K
      _ = Real.exp (K * t) := (Real.exp_nat_mul t K).symm
      _ ≤ Real.exp (8 * x) := Real.exp_le_exp.mpr hKt
  have hexp1 : (1 - 8 * x) * Real.exp (8 * x) ≤ 1 := by
    have h1 := Real.add_one_le_exp (-(8 * x))
    have h2 := Real.exp_pos (8 * x)
    calc (1 - 8 * x) * Real.exp (8 * x) ≤ Real.exp (-(8 * x)) * Real.exp (8 * x) :=
          mul_le_mul_of_nonneg_right (by linarith) h2.le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hexp8 : 1 ≤ Real.exp 8 := Real.one_le_exp (by norm_num)
  have hct := fun s => cwt_bound m (A s) c (B s) (cl s) (hanti s) (hcl s) t ht (hA s) (hB s)
  have hPl : 0 < ∏ s, (weylDim m (cl s) : ℝ) :=
    Finset.prod_pos fun s _ => by exact_mod_cast weylDim_pos_of_antitone m (cl s) (hanti s)
  have hPh : 0 < ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ) :=
    Finset.prod_pos fun s _ => hwt_pos m (A s) (B s)
  have hPc0 : 0 ≤ ∏ s, (weylDim (m + 2) (cwt m (A s) c (B s) (cl s)) : ℝ) :=
    Finset.prod_nonneg fun s _ => (hct s).1
  have Pc : ∏ s, (weylDim (m + 2) (cwt m (A s) c (B s) (cl s)) : ℝ) ≤
      (1 + t) ^ K * ((∏ s, (weylDim m (cl s) : ℝ)) * ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ)) := by
    calc _ ≤ ∏ s, ((1 + t) ^ (2 * m + 1) *
          ((weylDim m (cl s) : ℝ) * (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ))) :=
          Finset.prod_le_prod (fun s _ => (hct s).1) (fun s _ => (hct s).2)
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, ← pow_mul]
  have Ph : ∏ s, (weylDim (m + 2) (hwt m (A s + c) (B s + c)) : ℝ) ≤
      (1 + t) ^ K * ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ) := by
    calc _ ≤ ∏ s, ((1 + t) ^ (2 * m + 1) * (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ)) :=
          Finset.prod_le_prod (fun s _ => (hwt_pos m (A s + c) (B s + c)).le)
            (fun s _ => hwt_bound m (A s) c (B s) t ht (hA s) (hB s))
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [hCx]
  simp only [Rat.cast_prod, Rat.cast_mul]
  refine ⟨?_, ?_⟩
  · set Q := (∏ s, (weylDim m (cl s) : ℝ)) * ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ)
    have hQ : 0 ≤ Q := by positivity
    by_cases h : 1 - 8 * Real.exp 8 * x ≤ 0
    · calc (1 - 8 * Real.exp 8 * x) * ∏ s, (weylDim (m + 2) (cwt m (A s) c (B s) (cl s)) : ℝ) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg h hPc0
        _ ≤ Q := hQ
    · rw [not_le] at h
      have hC : 8 * x ≤ 8 * Real.exp 8 * x := by nlinarith
      calc (1 - 8 * Real.exp 8 * x) * ∏ s, (weylDim (m + 2) (cwt m (A s) c (B s) (cl s)) : ℝ)
          ≤ (1 - 8 * Real.exp 8 * x) * ((1 + t) ^ K * Q) := mul_le_mul_of_nonneg_left Pc h.le
        _ ≤ (1 - 8 * Real.exp 8 * x) * (Real.exp (8 * x) * Q) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hE hQ) h.le
        _ ≤ (1 - 8 * x) * (Real.exp (8 * x) * Q) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = ((1 - 8 * x) * Real.exp (8 * x)) * Q := by ring
        _ ≤ 1 * Q := mul_le_mul_of_nonneg_right hexp1 hQ
        _ = Q := one_mul Q
  · have hy : Real.exp (8 * x) ≤ 1 + 8 * Real.exp 8 * x := by
      have h8 : Real.exp (8 * x) ≤ Real.exp 8 := Real.exp_le_exp.mpr (by linarith)
      have : 8 * x * Real.exp (8 * x) ≤ 8 * x * Real.exp 8 :=
        mul_le_mul_of_nonneg_left h8 (by positivity)
      nlinarith
    calc ∏ s, (weylDim (m + 2) (hwt m (A s + c) (B s + c)) : ℝ)
        ≤ (1 + t) ^ K * ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ) := Ph
      _ ≤ Real.exp (8 * x) * ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ) :=
          mul_le_mul_of_nonneg_right hE hPh.le
      _ ≤ (1 + 8 * Real.exp 8 * x) * ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ) :=
          mul_le_mul_of_nonneg_right hy hPh.le

/- English proof (translation)
Introduce `ρ dcl dH dHp dlam κH κHp x hdlam hdH hdHp hdcl hκH0 hκH1 hκHp hx0 hx1 hρ h1 h2 h3`. Establish `hQ : dcl * dHp ≤ (1 + x) * (dcl * dH)`. Use `mul_le_mul_of_nonneg_left h2 hdcl` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hP1 : (1 - κH) * ((1 - x) * dlam) ≤ (1 - κH) * (dcl * dH)` using `mul_le_mul_of_nonneg_left h1 (by linarith)`.

Establish `hQ2 : κHp * (dcl * dHp) ≤ κHp * (2 * dlam)`. Apply `mul_le_mul_of_nonneg_left _ hκHp` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `hkx : 0 ≤ κH * x * dlam` using `by positivity`. Establish `key : (1 - κH - 2 * κHp - x) * dlam ≤ ρ` using `by nlinarith`.

Establish `: 1 - κH - 2 * κHp - x ≤ ρ / dlam` using `by rw [le_div_iff₀ hdlam]; linarith`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cloud_share_bound : CloudShare := by
  intro ρ dcl dH dHp dlam κH κHp x hdlam hdH hdHp hdcl hκH0 hκH1 hκHp hx0 hx1 hρ h1 h2 h3
  have hQ : dcl * dHp ≤ (1 + x) * (dcl * dH) := by
    have := mul_le_mul_of_nonneg_left h2 hdcl; nlinarith
  have hP1 : (1 - κH) * ((1 - x) * dlam) ≤ (1 - κH) * (dcl * dH) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have hQ2 : κHp * (dcl * dHp) ≤ κHp * (2 * dlam) := by
    apply mul_le_mul_of_nonneg_left _ hκHp; nlinarith
  have hkx : 0 ≤ κH * x * dlam := by positivity
  have key : (1 - κH - 2 * κHp - x) * dlam ≤ ρ := by nlinarith
  have : 1 - κH - 2 * κHp - x ≤ ρ / dlam := by rw [le_div_iff₀ hdlam]; linarith
  linarith

/- English proof (translation)
Introduce `O K V _ _ _ _ _ _ _ _ _ _ _ π hπ M Rl CC n E c hEc hCC hGR`. Use `choose hle u v huv using hGR`. Establish `htor : ∀ z : V, π • z = 0 → z = 0`. Introduce `z hz`. Establish `hπK : algebraMap O K π ≠ 0`.

Introduce `h0`. Conclude with `hπ.ne_zero ((IsFractionRing.injective O K) (by simpa using h0))`. Rewrite `hz` using `[← algebraMap_smul K π z]`. Conclude with `(smul_eq_zero.mp hz).resolve_left hπK`. Establish `key : ∀ a : Fin M → Fin n → O, ∑ e, ((u e (a e) : CC e) : V) = 0 → ∀ e i, π ∣ a e i`.

Introduce `a ha e i`. Establish `hsplit : ((u e (a e) : CC e) : V) = - ∑ e' ∈ univ.erase e, ((u e' (a e') : CC e') : V)`. Rewrite `ha` using `[← Finset.add_sum_erase _ _ (mem_univ e)]`. Conclude with `eq_neg_of_add_eq_zero_left ha`. Set `S : Submodule O V` to `(Rl e).map ((π ^ c) • LinearMap.id : V →ₗ[O] V)`.

Establish `hmem : ∀ e' ∈ univ.erase e, ((u e' (a e') : CC e') : V) ∈ S`. Introduce `e' he'`. Take `⟨y, hy, hxy⟩` from `hCC e' e (Finset.ne_of_mem_erase he') _ (u e' (a e')).2`. Conclude with `⟨y, hy, by simp [hxy]⟩`. Establish `hS : ((u e (a e) : CC e) : V) ∈ S`.

Rewrite using `[hsplit]`. Conclude with `S.neg_mem (S.sum_mem hmem)`. Take `⟨y, hy, hxy⟩` from `hS`. Establish `h2 : Submodule.inclusion (hle e) (u e (a e)) = π ^ c • (⟨y, hy⟩ : Rl e)`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Submodule.coe_inclusion, SetLike.val_smul]`. Rewrite using `[← hxy]`. Simplify using the standard rewrite rules. Establish `h3` using `congrArg (fun f => f (a e)) (huv e)`. Simplify using `only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h3`.

Rewrite `h3` using `[h2, map_smul]`. Establish `h4` using `congrFun h3 i`. Simplify using `only [Pi.smul_apply, smul_eq_mul] at h4`. Establish `h5 : a e i * π ^ E = (π ^ (c - E) * v e ⟨y, hy⟩ i) * π ^ E`. Rewrite using `[mul_comm (a e i), ← h4, ← pow_sub_mul_pow π hEc.le]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h6` using `mul_right_cancel₀ (pow_ne_zero E hπ.ne_zero) h5`. Rewrite using `[h6]`. Conclude with `dvd_mul_of_dvd_left (dvd_pow_self π (Nat.sub_ne_zero_of_lt hEc)) _`. Establish `iter : ∀ k : ℕ, ∀ a : Fin M → Fin n → O, ∑ e, ((u e (a e) : CC e) : V) = 0 → ∀ e i, π ^ k ∣ a e i`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro a _ e i`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `a ha e i`. Establish `hd` using `key a ha`. Use `choose a' ha' using hd`. Establish `hfun : ∀ e, a e = π • a' e` using `fun e => funext fun i => by simp [ha' e i]`. Establish `hsum : ∑ e, ((u e (a' e) : CC e) : V) = 0`.

Apply `htor` to reduce the goal to its premises. Rewrite using `[Finset.smul_sum]`. Rewrite using `[← ha]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[hfun e, map_smul]`.

Simplify using the standard rewrite rules. Use `ih a' hsum e i` as an intermediate fact. Rewrite using `[ha' e i, pow_succ, mul_comm (π ^ k)]`. Conclude with `mul_dvd_mul_left π this`. Establish `zero : ∀ a : Fin M → Fin n → O, ∑ e, ((u e (a e) : CC e) : V) = 0 → ∀ e i, a e i = 0`.

Introduce `a ha e i`. Assume the negation of the conclusion as `h`. Take `⟨k, w, hk⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h hπ`. Establish `hdiv` using `iter (k + 1) a ha e i`. Rewrite `hdiv` using `[hk, pow_succ, mul_comm (w : O)]`.

Establish `: π ∣ (w : O)` using `(mul_dvd_mul_iff_left (pow_ne_zero k hπ.ne_zero)).mp hdiv`. Conclude with `hπ.not_isUnit (isUnit_of_dvd_unit this w.isUnit)`. Set `w : Fin M × Fin n → V` to `fun p => ((u p.1 (Pi.single p.2 1) : CC p.1) : V)`. Establish `hli : LinearIndependent O w`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `g hg p`. Establish `hconv : ∑ p, g p • w p = ∑ e, ((u e (fun i => g (e, i)) : CC e) : V)`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Establish `: (fun i => g (e, i)) = ∑ i, g (e, i) • (Pi.single i 1 : Fin n → O)`.

Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[this, map_sum]`. Simplify using `[w, map_smul]`. Rewrite `hg` using `[hconv]`.

Conclude with `zero (fun e i => g (e, i)) hg p.1 p.2`. Establish `hliK : LinearIndependent K w` using `(LinearIndependent.iff_fractionRing O K).mp hli`. Use `hliK.fintype_card_le_finrank` as an intermediate fact. Simplify `this` using `[Fintype.card_prod, Fintype.card_fin]`.
-/
theorem count_B_formula : CountB := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ π hπ M Rl CC n E c hEc hCC hGR
  choose hle u v huv using hGR

  have htor : ∀ z : V, π • z = 0 → z = 0 := by
    intro z hz
    have hπK : algebraMap O K π ≠ 0 := by
      intro h0
      exact hπ.ne_zero ((IsFractionRing.injective O K) (by simpa using h0))
    rw [← algebraMap_smul K π z] at hz
    exact (smul_eq_zero.mp hz).resolve_left hπK
  have key : ∀ a : Fin M → Fin n → O, ∑ e, ((u e (a e) : CC e) : V) = 0 → ∀ e i, π ∣ a e i := by
    intro a ha e i
    have hsplit : ((u e (a e) : CC e) : V) = - ∑ e' ∈ univ.erase e, ((u e' (a e') : CC e') : V) := by
      rw [← Finset.add_sum_erase _ _ (mem_univ e)] at ha
      exact eq_neg_of_add_eq_zero_left ha
    let S : Submodule O V := (Rl e).map ((π ^ c) • LinearMap.id : V →ₗ[O] V)
    have hmem : ∀ e' ∈ univ.erase e, ((u e' (a e') : CC e') : V) ∈ S := by
      intro e' he'
      obtain ⟨y, hy, hxy⟩ := hCC e' e (Finset.ne_of_mem_erase he') _ (u e' (a e')).2
      exact ⟨y, hy, by simp [hxy]⟩
    have hS : ((u e (a e) : CC e) : V) ∈ S := by
      rw [hsplit]; exact S.neg_mem (S.sum_mem hmem)
    obtain ⟨y, hy, hxy⟩ := hS
    have h2 : Submodule.inclusion (hle e) (u e (a e)) = π ^ c • (⟨y, hy⟩ : Rl e) := by
      apply Subtype.ext
      simp only [Submodule.coe_inclusion, SetLike.val_smul]
      rw [← hxy]; simp
    have h3 := congrArg (fun f => f (a e)) (huv e)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h3
    rw [h2, map_smul] at h3
    have h4 := congrFun h3 i
    simp only [Pi.smul_apply, smul_eq_mul] at h4
    have h5 : a e i * π ^ E = (π ^ (c - E) * v e ⟨y, hy⟩ i) * π ^ E := by
      rw [mul_comm (a e i), ← h4, ← pow_sub_mul_pow π hEc.le]; ring
    have h6 := mul_right_cancel₀ (pow_ne_zero E hπ.ne_zero) h5
    rw [h6]
    exact dvd_mul_of_dvd_left (dvd_pow_self π (Nat.sub_ne_zero_of_lt hEc)) _
  have iter : ∀ k : ℕ, ∀ a : Fin M → Fin n → O, ∑ e, ((u e (a e) : CC e) : V) = 0 →
      ∀ e i, π ^ k ∣ a e i := by
    intro k
    induction k with
    | zero => intro a _ e i; simp
    | succ k ih =>
      intro a ha e i
      have hd := key a ha
      choose a' ha' using hd
      have hfun : ∀ e, a e = π • a' e := fun e => funext fun i => by simp [ha' e i]
      have hsum : ∑ e, ((u e (a' e) : CC e) : V) = 0 := by
        apply htor
        rw [Finset.smul_sum]
        rw [← ha]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hfun e, map_smul]; simp
      have := ih a' hsum e i
      rw [ha' e i, pow_succ, mul_comm (π ^ k)]
      exact mul_dvd_mul_left π this
  have zero : ∀ a : Fin M → Fin n → O, ∑ e, ((u e (a e) : CC e) : V) = 0 → ∀ e i, a e i = 0 := by
    intro a ha e i
    by_contra h
    obtain ⟨k, w, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h hπ
    have hdiv := iter (k + 1) a ha e i
    rw [hk, pow_succ, mul_comm (w : O)] at hdiv
    have : π ∣ (w : O) := (mul_dvd_mul_iff_left (pow_ne_zero k hπ.ne_zero)).mp hdiv
    exact hπ.not_isUnit (isUnit_of_dvd_unit this w.isUnit)
  let w : Fin M × Fin n → V := fun p => ((u p.1 (Pi.single p.2 1) : CC p.1) : V)
  have hli : LinearIndependent O w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    have hconv : ∑ p, g p • w p = ∑ e, ((u e (fun i => g (e, i)) : CC e) : V) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun e _ => ?_
      have : (fun i => g (e, i)) = ∑ i, g (e, i) • (Pi.single i 1 : Fin n → O) := by
        ext j; simp [Finset.sum_apply, Pi.single_apply]
      rw [this, map_sum]
      simp [w, map_smul]
    rw [hconv] at hg
    exact zero (fun e i => g (e, i)) hg p.1 p.2
  have hliK : LinearIndependent K w := (LinearIndependent.iff_fractionRing O K).mp hli
  have := hliK.fintype_card_le_finrank
  simpa [Fintype.card_prod, Fintype.card_fin] using this

end Formalism.CountingSumsFrames
