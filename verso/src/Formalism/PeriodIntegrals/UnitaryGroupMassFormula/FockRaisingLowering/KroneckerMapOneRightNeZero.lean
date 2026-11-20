import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.SameSign

noncomputable section

open Matrix

namespace FockRL

def jsgn {p q : ℕ} : FockH1Action.Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem Jm_eq_diagonal (p q : ℕ) : FockH1Action.Jm p q = Matrix.diagonal (jsgn (p := p) (q := q)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [FockH1Action.Jm, FockH1Action.Jpq, jsgn,
      Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp_all

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem conjR_apply {p q : ℕ} (Z : FockH1Action.Mat p q) (a b : FockH1Action.Ix p q) :
    FockH1Action.conjR Z a b = -(jsgn a * star (Z b a) * jsgn b) := by
  simp only [FockH1Action.conjR, FockH1Action.adjZ,
    Jm_eq_diagonal, Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Simplify the hypotheses and the goal together.
-/
theorem conjR_apply_of_not {p q : ℕ} (Z : FockH1Action.Mat p q) {a b : FockH1Action.Ix p q}
    (h : ¬ FockH1Action.sameBlock a b) : FockH1Action.conjR Z a b = (starRingEnd ℂ) (Z b a) := by
  rw [conjR_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp_all [FockH1Action.sameBlock, jsgn]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem sameBlock_symm {p q : ℕ} {a b : FockH1Action.Ix p q} (h : FockH1Action.sameBlock a b) :
    FockH1Action.sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [FockH1Action.sameBlock]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem conjR_isPC {p q : ℕ} (Z : FockH1Action.Mat p q) (hZ : FockH1Action.IsPC Z) :
    FockH1Action.IsPC (FockH1Action.conjR Z) := by
  intro a b hab
  rw [conjR_apply, hZ b a (sameBlock_symm hab)]
  simp

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem linePos_left {p q r s : ℕ} (a a' : FockH1Action.Ix p q) (b : FockH1Action.Ix r s) :
    FockH1Action.linePos ((a, b) : FockH1Action.Ln p q r s) = FockH1Action.linePos ((a', b) : FockH1Action.Ln p q r s) ↔
      FockH1Action.sameBlock a a' := by
  rcases a with a | a <;> rcases a' with a' | a' <;> rcases b with b | b <;>
    simp [FockH1Action.linePos, FockH1Action.sameBlock]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem linePos_right {p q r s : ℕ} (a : FockH1Action.Ix p q) (b b' : FockH1Action.Ix r s) :
    FockH1Action.linePos ((a, b) : FockH1Action.Ln p q r s) = FockH1Action.linePos ((a, b') : FockH1Action.Ln p q r s) ↔
      FockH1Action.sameBlock b b' := by
  rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>
    simp [FockH1Action.linePos, FockH1Action.sameBlock]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fockAct1_eq (p q r s : ℕ) (Z : FockH1Action.Mat p q) : FockH1Action.fockAct1 p q r s Z =
    FockH1Action.omAct p q r s (Matrix.kroneckerMap (fun x y : ℂ => x * y) Z (1 : FockH1Action.Mat r s)) := by
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fockAct2_eq (p q r s : ℕ) (Z : FockH1Action.Mat r s) : FockH1Action.fockAct2 p q r s Z =
    FockH1Action.omAct p q r s (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : FockH1Action.Mat p q) Z) := by
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules. Supply the required witnesses or components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem kroneckerMap_one_right_ne_zero {p q r s : ℕ} (Z : FockH1Action.Mat p q) {a a' : FockH1Action.Ix p q} {b b' : FockH1Action.Ix r s}
    (h : Matrix.kroneckerMap (fun x y : ℂ => x * y) Z (1 : FockH1Action.Mat r s) (a, b) (a', b') ≠ 0) :
    Z a a' ≠ 0 ∧ b = b' := by
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply] at h
  split_ifs at h with hb
  · exact ⟨by simpa using h, hb⟩
  · simp at h

/- English proof (translation)
Simplify using the standard rewrite rules. Supply the required witnesses or components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem kroneckerMap_one_left_ne_zero {p q r s : ℕ} (Z : FockH1Action.Mat r s) {a a' : FockH1Action.Ix p q} {b b' : FockH1Action.Ix r s}
    (h : Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : FockH1Action.Mat p q) Z (a, b) (a', b') ≠ 0) :
    Z b b' ≠ 0 ∧ a = a' := by
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply] at h
  split_ifs at h with ha
  · exact ⟨by simpa using h, ha⟩
  · simp at h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem kroneckerProperties : MatStep := by
  intro p q r s
  refine ⟨fockAct1_eq p q r s, fockAct2_eq p q r s, ?_, ?_, ?_, ?_,
    conjR_isPC, conjR_isPC, ?_, ?_⟩
  · rintro Z hZ ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨hz, rfl⟩ := kroneckerMap_one_right_ne_zero Z h
    have hs : FockH1Action.sameBlock a a' := by
      by_contra hn
      exact hz (hZ a a' hn)
    exact (linePos_left a a' b).2 hs
  · rintro Z hZ ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨hz, rfl⟩ := kroneckerMap_one_left_ne_zero Z h
    have hs : FockH1Action.sameBlock b b' := by
      by_contra hn
      exact hz (hZ b b' hn)
    exact (linePos_right a b b').2 hs
  · rintro Z hZ ⟨a, b⟩ ⟨a', b'⟩ h heq
    obtain ⟨hz, rfl⟩ := kroneckerMap_one_right_ne_zero Z h
    exact hz (hZ a a' ((linePos_left a a' b).1 heq))
  · rintro Z hZ ⟨a, b⟩ ⟨a', b'⟩ h heq
    obtain ⟨hz, rfl⟩ := kroneckerMap_one_left_ne_zero Z h
    exact hz (hZ b b' ((linePos_right a b b').1 heq))
  · rintro Z ⟨a, b⟩ ⟨a', b'⟩ h1 h2
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply]
    by_cases hb : b = b'
    · subst hb
      have hn : ¬ FockH1Action.sameBlock a' a := fun hs => by
        have := (linePos_left a a' b).2 (sameBlock_symm hs)
        rw [h1, h2] at this
        simp at this
      simp [conjR_apply_of_not Z hn]
    · have hb' : ¬ b' = b := fun e => hb e.symm
      simp [hb, hb']
  · rintro Z ⟨a, b⟩ ⟨a', b'⟩ h1 h2
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply]
    by_cases ha : a = a'
    · subst ha
      have hn : ¬ FockH1Action.sameBlock b' b := fun hs => by
        have := (linePos_right a b b').2 (sameBlock_symm hs)
        rw [h1, h2] at this
        simp at this
      simp [conjR_apply_of_not Z hn]
    · have ha' : ¬ a' = a := fun e => ha e.symm
      simp [ha, ha']

end FockRL
