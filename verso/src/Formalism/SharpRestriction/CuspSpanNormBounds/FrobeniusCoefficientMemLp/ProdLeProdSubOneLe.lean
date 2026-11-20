import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.HHRed

set_option linter.unusedVariables false

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds

section Perm

variable {d : ℕ} (c : Composition d)

def bsig (i : Fin d) : Fin d :=
  ⟨c.sizeUpTo (c.index i) + c.sizeUpTo ((c.index i : ℕ) + 1) - 1 - i, by
    have a1 := c.sizeUpTo_index_le i
    have a2 := c.lt_sizeUpTo_index_succ i
    simp only [Fin.val_succ] at a2
    have a3 : c.sizeUpTo ((c.index i : ℕ) + 1) ≤ d := c.sizeUpTo_le _
    omega⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bsig_val (i : Fin d) :
    ((bsig c i : Fin d) : ℕ) = c.sizeUpTo (c.index i) + c.sizeUpTo ((c.index i : ℕ) + 1) - 1 - i := rfl

/- English proof (translation)
Establish `a1` using `c.sizeUpTo_index_le i`. Establish `a2` using `c.lt_sizeUpTo_index_succ i`. Simplify using `only [Fin.val_succ] at a2`. Apply `index_unique c (bsig c i) (c.index i)` to reduce the goal to its premises. Rewrite using `[bsig_val]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[bsig_val]`. Use linear arithmetic over natural numbers and integers.
-/
theorem bsig_index (i : Fin d) : c.index (bsig c i) = c.index i := by
  have a1 := c.sizeUpTo_index_le i
  have a2 := c.lt_sizeUpTo_index_succ i
  simp only [Fin.val_succ] at a2
  apply index_unique c (bsig c i) (c.index i)
  · rw [bsig_val]; omega
  · rw [bsig_val]; omega

/- English proof (translation)
Establish `a1` using `c.sizeUpTo_index_le i`. Establish `a2` using `c.lt_sizeUpTo_index_succ i`. Simplify using `only [Fin.val_succ] at a2`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[bsig_val, bsig_index, bsig_val]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem bsig_bsig (i : Fin d) : bsig c (bsig c i) = i := by
  have a1 := c.sizeUpTo_index_le i
  have a2 := c.lt_sizeUpTo_index_succ i
  simp only [Fin.val_succ] at a2
  apply Fin.ext
  rw [bsig_val, bsig_index, bsig_val]
  omega

def bperm : Equiv.Perm (Fin d) := Function.Involutive.toPerm (bsig c) (bsig_bsig c)

end Perm

section Minor

variable {E : Type} [Field E] {d : ℕ}

end Minor

/- English proof (translation)
Establish `h1 : (1 : ℝ) ≤ max 1 x` using `le_max_left _ _`. Establish `h2 : (1 : ℝ) ≤ max 1 z` using `le_max_left _ _`. Apply `max_le` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Conclude with `mul_le_mul (le_max_right _ _) (le_max_right _ _) hz (by linarith)`.
-/
theorem max_mul_le {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) : max 1 (x * z) ≤ max 1 x * max 1 z := by
  have h1 : (1 : ℝ) ≤ max 1 x := le_max_left _ _
  have h2 : (1 : ℝ) ≤ max 1 z := le_max_left _ _
  apply max_le
  · nlinarith
  · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) hz (by linarith)

def pre (y : ℕ → ℝ) (a : ℕ) : ℝ := ∏ i ∈ range (a + 1), y i

section Ends

variable {E : Type} [Field E] {d : ℕ}

def bEnd (p : Point E d) (a : Fin (toComp p).length) : E :=
  leadMinorE (ptMat p) ((toComp p).sizeUpTo ((a : ℕ) + 1))

def yN (τ : E →+* ℂ) (p : Point E d) (i : ℕ) : ℝ :=
  if h : i < (toComp p).length then ‖τ (toT p ⟨i, h⟩)‖ ^ (toComp p).blocksFun ⟨i, h⟩ else 1

end Ends

end Formalism.MainNotions.S.Pv.HH

end
