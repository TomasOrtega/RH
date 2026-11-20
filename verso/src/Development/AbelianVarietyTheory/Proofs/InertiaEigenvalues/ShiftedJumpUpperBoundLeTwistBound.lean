import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemIntPts

namespace GlobalTheory

open GlobalTheory.PositionData

/- English proof (translation)
Introduce `t up Fl Fc η S B W0 ht htη hB hS0 hFl hFc hW`. Establish `ht1 : (1 : ℝ) ≤ t` using `by exact_mod_cast ht`. Establish `hFl' : ∀ z ∈ Fl, ((t : ℝ) - 1) / 2 - η ≤ (z : ℝ) ∧ (z : ℝ) ≤ ((t : ℝ) - 1) / 2 + η`. Introduce `z hz`. Establish `h` using `(hFl z hz).1`.

Rewrite `h` using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith [h.1, h.2]`. Establish `castToNat : ∀ x : ℤ, ((x.toNat : ℕ) : ℝ) = max (x : ℝ) 0`. Introduce `x`. Establish `h : ((x.toNat : ℕ) : ℤ) = max x 0` using `Int.toNat_eq_max x`.

Rewrite using `[← Int.cast_natCast, h]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hmn : ∀ (s : Finset ℤ) (H : s.Nonempty) (a : ℝ), (∀ y ∈ s, a ≤ (y : ℝ)) → a ≤ ((s.min' H : ℤ) : ℝ)` using `fun s H a h => h _ (Finset.min'_mem s H)`. Establish `hmx : ∀ (s : Finset ℤ) (H : s.Nonempty) (a : ℝ), (∀ y ∈ s, (y : ℝ) ≤ a) → ((s.max' H : ℤ) : ℝ) ≤ a` using `fun s H a h => h _ (Finset.max'_mem s H)`.

Establish `hmxLo : ((mxLo t Fl : ℤ) : ℝ) ≤ ((t : ℝ) - 1) / 2 + η`. Apply `hmx` to reduce the goal to its premises. Introduce `y hy`. Rewrite `hy` using `[Finset.mem_insert]`. Break down `hy with rfl | hy` into its components or cases.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(hFl' y hy).2`. Consider the cases of `up`. Establish `hFc' : ∀ z ∈ Fc, ((t : ℝ) - 1) / 2 - W0 - S - η - 1 ≤ (z : ℝ)`.

Introduce `z hz`. Establish `h` using `(hFc z hz).2`. Simplify using `only [Bool.false_eq_true, if_false] at h`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : ((t : ℝ) - 1) / 2 - W0 - S - η - 1 ≤ ((mnAll Fl Fc : ℤ) : ℝ)`.

Apply `hmn` to reduce the goal to its premises. Introduce `y hy`. Rewrite `hy` using `[Finset.mem_insert, Finset.mem_union]`. Break down `hy with rfl | hy | hy` into its components or cases. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear relations using `[(hFl' y hy).1]`. Conclude with `hFc' y hy`. Establish `h0 : mnAll Fl Fc ≤ 0` using `Finset.min'_le _ _ (Finset.mem_insert_self _ _)`. Establish `hw : ((wS false Fl Fc : ℕ) : ℤ) = 1 - mnAll Fl Fc`.

Simplify using `only [wS, Bool.false_eq_true, if_false]`. Conclude with `Int.toNat_of_nonneg (by omega)`. Simplify using `only [PositionData.hS, Bool.false_eq_true, if_false]`. Rewrite using `[castToNat, hw]`. Apply `max_le` to reduce the goal to its premises.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hFc' : ∀ z ∈ Fc, (z : ℝ) ≤ ((t : ℝ) - 1) / 2 + W0 + S + η + 1`. Introduce `z hz`.

Establish `h` using `(hFc z hz).2`. Simplify using `only [if_true] at h`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : ((mxAll t Fl Fc : ℤ) : ℝ) ≤ ((t : ℝ) - 1) / 2 + W0 + S + η + 1`. Apply `hmx` to reduce the goal to its premises.

Introduce `y hy`. Rewrite `hy` using `[Finset.mem_insert, Finset.mem_union]`. Break down `hy with rfl | hy | hy` into its components or cases. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear relations using `[(hFl' y hy).2]`. Conclude with `hFc' y hy`. Establish `h2 : ((t : ℝ) - 1) / 2 - η ≤ ((mnLo Fl : ℤ) : ℝ)`. Apply `hmn` to reduce the goal to its premises. Introduce `y hy`.

Rewrite `hy` using `[Finset.mem_insert]`. Break down `hy with rfl | hy` into its components or cases. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(hFl' y hy).1`.

Establish `h0 : mnLo Fl ≤ 0` using `Finset.min'_le _ _ (Finset.mem_insert_self _ _)`. Establish `hw : ((wS true Fl Fc : ℕ) : ℤ) = 1 - mnLo Fl`. Simplify using `only [wS, if_true]`. Conclude with `Int.toNat_of_nonneg (by omega)`. Simplify using `only [PositionData.hS, if_true]`.

Rewrite using `[castToNat, hw]`. Apply `max_le` to reduce the goal to its premises. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hS_le_bound : ∀ (t : ℕ) (up : Bool) (Fl Fc : Finset ℤ) (η S B W0 : ℝ), 1 ≤ t → (t : ℝ) ≤ η → 0 ≤ B → 0 ≤ S →
    (∀ z ∈ Fl, |(z : ℝ) - ((t : ℝ) - 1) / 2| ≤ η ∧ 2 * B + (t : ℝ) / 2 + 3 ≤ |(z : ℝ) - ((t : ℝ) - 1) / 2|) →
    (∀ z ∈ Fc, W0 ≤ (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ∧
      (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ≤ W0 + S + η + 1) →
    2 * B + (t : ℝ) / 2 + 3 ≤ W0 →
    ((GlobalTheory.PositionData.hS up t Fl Fc : ℕ) : ℝ) ≤ W0 + S + 2 * η + 3 := by
  intro t up Fl Fc η S B W0 ht htη hB hS0 hFl hFc hW
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hFl' : ∀ z ∈ Fl, ((t : ℝ) - 1) / 2 - η ≤ (z : ℝ) ∧ (z : ℝ) ≤ ((t : ℝ) - 1) / 2 + η := by
    intro z hz
    have h := (hFl z hz).1
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have castToNat : ∀ x : ℤ, ((x.toNat : ℕ) : ℝ) = max (x : ℝ) 0 := by
    intro x
    have h : ((x.toNat : ℕ) : ℤ) = max x 0 := Int.toNat_eq_max x
    rw [← Int.cast_natCast, h]
    push_cast
    rfl
  have hmn : ∀ (s : Finset ℤ) (H : s.Nonempty) (a : ℝ), (∀ y ∈ s, a ≤ (y : ℝ)) →
      a ≤ ((s.min' H : ℤ) : ℝ) := fun s H a h => h _ (Finset.min'_mem s H)
  have hmx : ∀ (s : Finset ℤ) (H : s.Nonempty) (a : ℝ), (∀ y ∈ s, (y : ℝ) ≤ a) →
      ((s.max' H : ℤ) : ℝ) ≤ a := fun s H a h => h _ (Finset.max'_mem s H)

  have hmxLo : ((mxLo t Fl : ℤ) : ℝ) ≤ ((t : ℝ) - 1) / 2 + η := by
    apply hmx
    intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · push_cast; linarith
    · exact (hFl' y hy).2
  cases up
  ·
    have hFc' : ∀ z ∈ Fc, ((t : ℝ) - 1) / 2 - W0 - S - η - 1 ≤ (z : ℝ) := by
      intro z hz
      have h := (hFc z hz).2
      simp only [Bool.false_eq_true, if_false] at h
      linarith
    have h1 : ((t : ℝ) - 1) / 2 - W0 - S - η - 1 ≤ ((mnAll Fl Fc : ℤ) : ℝ) := by
      apply hmn
      intro y hy
      rw [Finset.mem_insert, Finset.mem_union] at hy
      rcases hy with rfl | hy | hy
      · push_cast; linarith
      · linarith [(hFl' y hy).1]
      · exact hFc' y hy
    have h0 : mnAll Fl Fc ≤ 0 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    have hw : ((wS false Fl Fc : ℕ) : ℤ) = 1 - mnAll Fl Fc := by
      simp only [wS, Bool.false_eq_true, if_false]
      exact Int.toNat_of_nonneg (by omega)
    simp only [PositionData.hS, Bool.false_eq_true, if_false]
    rw [castToNat, hw]
    apply max_le
    · push_cast; linarith
    · linarith
  ·
    have hFc' : ∀ z ∈ Fc, (z : ℝ) ≤ ((t : ℝ) - 1) / 2 + W0 + S + η + 1 := by
      intro z hz
      have h := (hFc z hz).2
      simp only [if_true] at h
      linarith
    have h1 : ((mxAll t Fl Fc : ℤ) : ℝ) ≤ ((t : ℝ) - 1) / 2 + W0 + S + η + 1 := by
      apply hmx
      intro y hy
      rw [Finset.mem_insert, Finset.mem_union] at hy
      rcases hy with rfl | hy | hy
      · push_cast; linarith
      · linarith [(hFl' y hy).2]
      · exact hFc' y hy
    have h2 : ((t : ℝ) - 1) / 2 - η ≤ ((mnLo Fl : ℤ) : ℝ) := by
      apply hmn
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · push_cast; linarith
      · exact (hFl' y hy).1
    have h0 : mnLo Fl ≤ 0 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    have hw : ((wS true Fl Fc : ℕ) : ℤ) = 1 - mnLo Fl := by
      simp only [wS, if_true]
      exact Int.toNat_of_nonneg (by omega)
    simp only [PositionData.hS, if_true]
    rw [castToNat, hw]
    apply max_le
    · push_cast; linarith
    · linarith

end GlobalTheory
