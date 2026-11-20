import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar

noncomputable section

namespace GlobalTheory.ColIns

open GlobalTheory.StdPairLoc

variable {R : Type} {a b : ℕ}

def keptCol (a b : ℕ) (j : Fin (a + b)) : Fin (a + (b + 2)) :=
  ⟨if j.1 < a then j.1 else j.1 + 1, by split_ifs <;> omega⟩

def newCol (a b : ℕ) : Fin (a + (b + 2)) := ⟨a, by omega⟩

def lastCol (a b : ℕ) : Fin (a + (b + 2)) := ⟨a + b + 1, by omega⟩

def dropCols (X : Matrix (Fin a) (Fin (a + (b + 2))) R) : Matrix (Fin a) (Fin (a + b)) R :=
  fun i j => X i (keptCol a b j)

def colA (X : Matrix (Fin a) (Fin (a + (b + 2))) R) : Fin a → R := fun i => X i (newCol a b)

def colS (X : Matrix (Fin a) (Fin (a + (b + 2))) R) : Fin a → R := fun i => X i (lastCol a b)

section Zero

variable [Zero R]

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Simplify using `only [dropCols, insB, keptCol]`. Distinguish the cases in `h : j.1 < a`. Simplify using `[h]`. Establish `h2 : ¬ j.1 + 1 < a` using `by omega`.

Establish `h3 : j.1 + 1 ≠ a` using `by omega`. Establish `h4 : j.1 + 1 ≠ a + b + 1` using `by have := j.2; omega`. Establish `h5 : j.1 ≠ a + b` using `by have := j.2; omega`. Simplify using `[h, h2, h3, h4, h5]`.
-/
theorem dropCols_insB (Y : Matrix (Fin a) (Fin (a + b)) R) (t : Fin a → R) : dropCols (insB Y t) = Y := by
  funext i j
  simp only [dropCols, insB, keptCol]
  by_cases h : j.1 < a
  · simp [h]
  · have h2 : ¬ j.1 + 1 < a := by omega
    have h3 : j.1 + 1 ≠ a := by omega
    have h4 : j.1 + 1 ≠ a + b + 1 := by have := j.2; omega
    have h5 : j.1 ≠ a + b := by have := j.2; omega
    simp [h, h2, h3, h4, h5]

end Zero

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Simplify using `only [insB, Matrix.add_apply, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem insB_add [AddZeroClass R] (Y Y' : Matrix (Fin a) (Fin (a + b)) R) (t t' : Fin a → R) :
    insB (Y + Y') (t + t') = insB Y t + insB Y' t' := by
  funext i j
  simp only [insB, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

end GlobalTheory.ColIns

end
