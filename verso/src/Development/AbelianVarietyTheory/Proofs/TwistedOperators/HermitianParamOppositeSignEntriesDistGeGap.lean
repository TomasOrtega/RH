import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SignatureAndNodeGaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Links Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig lamS lamT StepGap)
open GlobalTheory.IndefiniteRowSideFullHecke.SignatureAndNodeGaps GlobalTheory.Chain.ItPairCompare

namespace GlobalTheory.Chain.ParOfSizes

section HC

variable {R : Ranks} (P : HCParam R) {h₀ : ℝ}

/- English proof (translation)
Break down `h.lt_or_eq with hlt | heq` into its components or cases. Establish `h1` using `gap_of_lt P hlt`. Establish `h2` using `gap_of_le P (le_refl i.1)`. Establish `ht : (0 : ℚ) ≤ R.t` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `le_of_eq (congrArg P.b (Fin.ext heq))`.
-/
theorem b_le_of_le {i j : Fin R.m} (h : i.1 ≤ j.1) : P.b i ≤ P.b j := by
  rcases h.lt_or_eq with hlt | heq
  ·
    have h1 := gap_of_lt P hlt
    have h2 := gap_of_le P (le_refl i.1)
    have ht : (0 : ℚ) ≤ R.t := Nat.cast_nonneg _
    linarith
  · exact le_of_eq (congrArg P.b (Fin.ext heq))

/- English proof (translation)
Establish `hi : i.1 + 1 < R.m` using `by omega`. Establish `hstep` using `hg i.1 hi`. Establish `hmono : P.b ⟨i.1 + 1, hi⟩ ≤ P.b j` using `b_le_of_le P (show i.1 + 1 ≤ j.1 by omega)`. Establish `hq : (P.b ⟨i.1 + 1, hi⟩ - P.b ⟨i.1, by omega⟩ : ℚ) ≤ P.b j - P.b i`. Establish `e : (⟨i.1, by omega⟩ : Fin R.m) = i` using `Fin.ext rfl`.

Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hstep.trans (by exact_mod_cast hq)`.
-/
theorem le_b_sub (hg : ∀ (i : ℕ) (h : i + 1 < R.m), h₀ ≤ ((P.b ⟨i + 1, h⟩ - P.b ⟨i, by omega⟩ : ℚ) : ℝ))
    {i j : Fin R.m} (h : i.1 < j.1) : h₀ ≤ ((P.b j - P.b i : ℚ) : ℝ) := by
  have hi : i.1 + 1 < R.m := by omega

  have hstep := hg i.1 hi
  have hmono : P.b ⟨i.1 + 1, hi⟩ ≤ P.b j := b_le_of_le P (show i.1 + 1 ≤ j.1 by omega)
  have hq : (P.b ⟨i.1 + 1, hi⟩ - P.b ⟨i.1, by omega⟩ : ℚ) ≤ P.b j - P.b i := by
    have e : (⟨i.1, by omega⟩ : Fin R.m) = i := Fin.ext rfl
    rw [e]
    linarith
  exact hstep.trans (by exact_mod_cast hq)

/- English proof (translation)
Rewrite using `[← Rat.cast_abs]`. Break down `x with a | i | a` into its components or cases. Simplify using `[sgn] at hx`. Simplify using `only [sgn, decide_eq_false_iff_not, not_or, not_le] at hx`. Take `⟨hij, hodd⟩` from `hx`.

Establish `hi1 : i.1 - 1 < R.m` using `by omega`. Break down `y with c | i2 | ⟨⟨i2, hi2⟩, a⟩` into its components or cases. Establish `h1` using `neg_b_lt_v P c ⟨i.1 - 1, hi1⟩`. Establish `h2` using `le_b_sub P hg (i := ⟨i.1 - 1, hi1⟩) (j := i) (show i.1 - 1 < i.1 by omega)`. Use `h2.trans (Rat.cast_le.mpr ?_)` and prove the remaining obligations.

Simplify using `only [val]`. Rewrite using `[abs_sub_comm]`. Conclude with `le_abs.mpr (Or.inl (by linarith))`. Simplify using `only [sgn, decide_eq_true_eq] at hy`. Break down `lt_trichotomy i2.1 i.1 with h2 | h2 | h2` into its components or cases.

Use `(le_b_sub P hg h2).trans (Rat.cast_le.mpr ?_)` and prove the remaining obligations. Simplify using `only [val]`. Rewrite using `[abs_sub_comm]`. Conclude with `le_abs.mpr (Or.inl (by linarith))`. It suffices to derive a contradiction.

Rewrite `hy` using `[h2]`. Break down `hy with hy | hy` into its components or cases. Use linear arithmetic over natural numbers and integers. Conclude with `hodd hy`. Use `(le_b_sub P hg h2).trans (Rat.cast_le.mpr ?_)` and prove the remaining obligations.

Simplify using `only [val]`. Conclude with `le_abs.mpr (Or.inl (by linarith))`. Establish `hi3 : i2.1 + 1 < R.m` using `by omega`. Establish `g1` using `gap_of_lt P (i := i2) (j := ⟨i2.1 + 1, hi3⟩) (show i2.1 < i2.1 + 1 by omega)`. Establish `g2` using `le_b_sub P hg (i := ⟨i2.1 + 1, hi3⟩) (j := i) (show i2.1 + 1 < i.1 by omega)`.

Establish `ha0 : (0 : ℚ) ≤ (a.1 : ℚ)` using `Nat.cast_nonneg _`. Establish `ha1 : (a.1 : ℚ) + 1 ≤ R.t` using `by exact_mod_cast a.2`. Use `g2.trans (Rat.cast_le.mpr ?_)` and prove the remaining obligations. Simplify using `only [val]`. Rewrite using `[abs_sub_comm]`.

Conclude with `le_abs.mpr (Or.inl (by linarith))`. Simplify using `[sgn] at hx`.
-/
theorem hermitianParam_oppositeSign_entries_dist_ge_gap (hg : ∀ (i : ℕ) (h : i + 1 < R.m), h₀ ≤ ((P.b ⟨i + 1, h⟩ - P.b ⟨i, by omega⟩ : ℚ) : ℝ))
    (j : ℕ) (x y : Idx R j) (hx : sgn R j x = false) (hy : sgn R j y = true) :
    h₀ ≤ |((val P j x - val P j y : ℚ) : ℝ)| := by
  rw [← Rat.cast_abs]
  rcases x with a | i | a
  · simp [sgn] at hx
  · simp only [sgn, decide_eq_false_iff_not, not_or, not_le] at hx
    obtain ⟨hij, hodd⟩ := hx
    have hi1 : i.1 - 1 < R.m := by omega
    rcases y with c | i2 | ⟨⟨i2, hi2⟩, a⟩
    ·
      have h1 := neg_b_lt_v P c ⟨i.1 - 1, hi1⟩
      have h2 := le_b_sub P hg (i := ⟨i.1 - 1, hi1⟩) (j := i) (show i.1 - 1 < i.1 by omega)
      refine h2.trans (Rat.cast_le.mpr ?_)
      simp only [val]
      rw [abs_sub_comm]
      exact le_abs.mpr (Or.inl (by linarith))
    · simp only [sgn, decide_eq_true_eq] at hy
      rcases lt_trichotomy i2.1 i.1 with h2 | h2 | h2
      · refine (le_b_sub P hg h2).trans (Rat.cast_le.mpr ?_)
        simp only [val]
        rw [abs_sub_comm]
        exact le_abs.mpr (Or.inl (by linarith))
      · exfalso
        rw [h2] at hy
        rcases hy with hy | hy
        · omega
        · exact hodd hy
      · refine (le_b_sub P hg h2).trans (Rat.cast_le.mpr ?_)
        simp only [val]
        exact le_abs.mpr (Or.inl (by linarith))
    ·
      have hi3 : i2.1 + 1 < R.m := by omega
      have g1 := gap_of_lt P (i := i2) (j := ⟨i2.1 + 1, hi3⟩) (show i2.1 < i2.1 + 1 by omega)
      have g2 := le_b_sub P hg (i := ⟨i2.1 + 1, hi3⟩) (j := i) (show i2.1 + 1 < i.1 by omega)
      have ha0 : (0 : ℚ) ≤ (a.1 : ℚ) := Nat.cast_nonneg _
      have ha1 : (a.1 : ℚ) + 1 ≤ R.t := by exact_mod_cast a.2
      refine g2.trans (Rat.cast_le.mpr ?_)
      simp only [val]
      rw [abs_sub_comm]
      exact le_abs.mpr (Or.inl (by linarith))
  · simp [sgn] at hx

/- English proof (translation)
Rewrite using `[add_sub_add_right_eq_sub]`. Distinguish the cases in `hx : sgn R j x = false`. Establish `hy : sgn R j y = true`. Consider the cases of `hy' : sgn R j y`. Conclude with `absurd (hx.trans hy'.symm) h`.

Both sides reduce to the same expression. Conclude with `hermitianParam_oppositeSign_entries_dist_ge_gap P hg j x y hx hy`. Establish `hx' : sgn R j x = true` using `by simpa using hx`. Establish `hy : sgn R j y = false`. Consider the cases of `hy' : sgn R j y`.

Both sides reduce to the same expression. Conclude with `absurd (hx'.trans hy'.symm) h`. Rewrite using `[← neg_sub, Rat.cast_neg, abs_neg]`. Conclude with `hermitianParam_oppositeSign_entries_dist_ge_gap P hg j y x hy hx'`.
-/
theorem le_val_sub (hg : ∀ (i : ℕ) (h : i + 1 < R.m), h₀ ≤ ((P.b ⟨i + 1, h⟩ - P.b ⟨i, by omega⟩ : ℚ) : ℝ))
    (j : ℕ) (c : ℚ) (x y : Idx R j) (h : sgn R j x ≠ sgn R j y) :
    h₀ ≤ |(((val P j x + c) - (val P j y + c) : ℚ) : ℝ)| := by
  rw [add_sub_add_right_eq_sub]
  by_cases hx : sgn R j x = false
  · have hy : sgn R j y = true := by
      cases hy' : sgn R j y
      · exact absurd (hx.trans hy'.symm) h
      · rfl
    exact hermitianParam_oppositeSign_entries_dist_ge_gap P hg j x y hx hy
  · have hx' : sgn R j x = true := by simpa using hx
    have hy : sgn R j y = false := by
      cases hy' : sgn R j y
      · rfl
      · exact absurd (hx'.trans hy'.symm) h
    rw [← neg_sub, Rat.cast_neg, abs_neg]
    exact hermitianParam_oppositeSign_entries_dist_ge_gap P hg j y x hy hx'

end HC

end GlobalTheory.Chain.ParOfSizes

end
