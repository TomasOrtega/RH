import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.SameSign

noncomputable section

open Matrix

namespace FockRL

def jsgn {p q : ℕ} : FockH1Action.Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Apply the tactic sequence `simp [FockH1Action.Jm, FockH1Action.Jpq, jsgn, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp_all`.
-/
theorem Jm_eq_diagonal (p q : ℕ) : FockH1Action.Jm p q = Matrix.diagonal (jsgn (p := p) (q := q)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [FockH1Action.Jm, FockH1Action.Jpq, jsgn,
      Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp_all

/- English proof (translation)
Simplify using `only [FockH1Action.conjR, FockH1Action.adjZ, Jm_eq_diagonal, Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]`.
-/
theorem conjR_apply {p q : ℕ} (Z : FockH1Action.Mat p q) (a b : FockH1Action.Ix p q) :
    FockH1Action.conjR Z a b = -(jsgn a * star (Z b a) * jsgn b) := by
  simp only [FockH1Action.conjR, FockH1Action.adjZ,
    Jm_eq_diagonal, Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply]

/- English proof (translation)
Rewrite using `[conjR_apply]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;>`. Simplify using `[FockH1Action.sameBlock, jsgn]`.
-/
theorem conjR_apply_of_not {p q : ℕ} (Z : FockH1Action.Mat p q) {a b : FockH1Action.Ix p q}
    (h : ¬ FockH1Action.sameBlock a b) : FockH1Action.conjR Z a b = (starRingEnd ℂ) (Z b a) := by
  rw [conjR_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp_all [FockH1Action.sameBlock, jsgn]

/- English proof (translation)
Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp_all [FockH1Action.sameBlock]`.
-/
theorem sameBlock_symm {p q : ℕ} {a b : FockH1Action.Ix p q} (h : FockH1Action.sameBlock a b) :
    FockH1Action.sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [FockH1Action.sameBlock]

/- English proof (translation)
Introduce `a b hab`. Rewrite using `[conjR_apply, hZ b a (sameBlock_symm hab)]`. Simplify using the standard rewrite rules.
-/
theorem conjR_isPC {p q : ℕ} (Z : FockH1Action.Mat p q) (hZ : FockH1Action.IsPC Z) :
    FockH1Action.IsPC (FockH1Action.conjR Z) := by
  intro a b hab
  rw [conjR_apply, hZ b a (sameBlock_symm hab)]
  simp

/- English proof (translation)
Apply the tactic sequence `rcases a with a | a <;> rcases a' with a' | a' <;> rcases b with b | b <;>`. Simplify using `[FockH1Action.linePos, FockH1Action.sameBlock]`.
-/
theorem linePos_left {p q r s : ℕ} (a a' : FockH1Action.Ix p q) (b : FockH1Action.Ix r s) :
    FockH1Action.linePos ((a, b) : FockH1Action.Ln p q r s) = FockH1Action.linePos ((a', b) : FockH1Action.Ln p q r s) ↔
      FockH1Action.sameBlock a a' := by
  rcases a with a | a <;> rcases a' with a' | a' <;> rcases b with b | b <;>
    simp [FockH1Action.linePos, FockH1Action.sameBlock]

/- English proof (translation)
Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>`. Simplify using `[FockH1Action.linePos, FockH1Action.sameBlock]`.
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
Simplify using `only [Matrix.kroneckerMap_apply, Matrix.one_apply] at h`. Use `split_ifs at h with hb`. Conclude with `⟨by simpa using h, hb⟩`. Simplify using `at h`.
-/
theorem kroneckerMap_one_right_ne_zero {p q r s : ℕ} (Z : FockH1Action.Mat p q) {a a' : FockH1Action.Ix p q} {b b' : FockH1Action.Ix r s}
    (h : Matrix.kroneckerMap (fun x y : ℂ => x * y) Z (1 : FockH1Action.Mat r s) (a, b) (a', b') ≠ 0) :
    Z a a' ≠ 0 ∧ b = b' := by
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply] at h
  split_ifs at h with hb
  · exact ⟨by simpa using h, hb⟩
  · simp at h

/- English proof (translation)
Simplify using `only [Matrix.kroneckerMap_apply, Matrix.one_apply] at h`. Use `split_ifs at h with ha`. Conclude with `⟨by simpa using h, ha⟩`. Simplify using `at h`.
-/
theorem kroneckerMap_one_left_ne_zero {p q r s : ℕ} (Z : FockH1Action.Mat r s) {a a' : FockH1Action.Ix p q} {b b' : FockH1Action.Ix r s}
    (h : Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : FockH1Action.Mat p q) Z (a, b) (a', b') ≠ 0) :
    Z b b' ≠ 0 ∧ a = a' := by
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply] at h
  split_ifs at h with ha
  · exact ⟨by simpa using h, ha⟩
  · simp at h

/- English proof (translation)
Introduce `p q r s`. Use `⟨fockAct1_eq p q r s, fockAct2_eq p q r s, ?_, ?_, ?_, ?_, conjR_isPC, conjR_isPC, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `Z hZ ⟨a, b⟩ ⟨a', b'⟩ h`. Take `⟨hz, rfl⟩` from `kroneckerMap_one_right_ne_zero Z h`. Establish `hs : FockH1Action.sameBlock a a'`.

Assume the negation of the conclusion as `hn`. Conclude with `hz (hZ a a' hn)`. Conclude with `(linePos_left a a' b).2 hs`. Introduce and unpack `Z hZ ⟨a, b⟩ ⟨a', b'⟩ h`. Take `⟨hz, rfl⟩` from `kroneckerMap_one_left_ne_zero Z h`.

Establish `hs : FockH1Action.sameBlock b b'`. Assume the negation of the conclusion as `hn`. Conclude with `hz (hZ b b' hn)`. Conclude with `(linePos_right a b b').2 hs`. Introduce and unpack `Z hZ ⟨a, b⟩ ⟨a', b'⟩ h heq`.

Take `⟨hz, rfl⟩` from `kroneckerMap_one_right_ne_zero Z h`. Conclude with `hz (hZ a a' ((linePos_left a a' b).1 heq))`. Introduce and unpack `Z hZ ⟨a, b⟩ ⟨a', b'⟩ h heq`. Take `⟨hz, rfl⟩` from `kroneckerMap_one_left_ne_zero Z h`. Conclude with `hz (hZ b b' ((linePos_right a b b').1 heq))`.

Introduce and unpack `Z ⟨a, b⟩ ⟨a', b'⟩ h1 h2`. Simplify using `only [Matrix.kroneckerMap_apply, Matrix.one_apply]`. Distinguish the cases in `hb : b = b'`. Substitute `hb` using the available equality. Establish `hn : ¬ FockH1Action.sameBlock a' a` using `fun hs => by`.

Use `(linePos_left a a' b).2 (sameBlock_symm hs)` as an intermediate fact. Rewrite `this` using `[h1, h2]`. Simplify using `at this`. Simplify using `[conjR_apply_of_not Z hn]`. Establish `hb' : ¬ b' = b` using `fun e => hb e.symm`.

Simplify using `[hb, hb']`. Introduce and unpack `Z ⟨a, b⟩ ⟨a', b'⟩ h1 h2`. Simplify using `only [Matrix.kroneckerMap_apply, Matrix.one_apply]`. Distinguish the cases in `ha : a = a'`. Substitute `ha` using the available equality.

Establish `hn : ¬ FockH1Action.sameBlock b' b` using `fun hs => by`. Use `(linePos_right a b b').2 (sameBlock_symm hs)` as an intermediate fact. Rewrite `this` using `[h1, h2]`. Simplify using `at this`. Simplify using `[conjR_apply_of_not Z hn]`.

Establish `ha' : ¬ a' = a` using `fun e => ha e.symm`. Simplify using `[ha, ha']`.
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
