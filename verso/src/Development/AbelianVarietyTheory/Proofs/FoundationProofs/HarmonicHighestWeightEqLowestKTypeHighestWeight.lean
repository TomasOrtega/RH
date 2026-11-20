import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FockSingularValues
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.JointHarm

namespace GlobalTheory.HarmonicShape

/- English proof (translation)
Establish `hj : P ∈ jointHW μ (wtH n ap am)`. Use `⟨⟨h1.2, h2⟩, ⟨fun a b => ?_, fun a b => by simp⟩, fun _ j => j.elim0, fun i => i.elim0⟩` and prove the remaining obligations. Use `h3 a b` as an intermediate fact. Rewrite `this` using `[GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.fockAct1_lower, neg_eq_zero]`. Conclude with `this`.

Take `⟨α, β, γ, δ, ⟨-, -, -, -, a1, b1, c1, d1, -, -, -, -, e1, e2, e3, -⟩, -⟩` from `four_of_joint h1.1 hj`. Use function extensionality and compare the values at `x`. Break down `x with i | j` into its components or cases. Establish `hi` using `i.2`. Establish `u` using `e1 i`.

Establish `v` using `e3 ⟨i.1, by omega⟩`. Rewrite `u` using `[b1 _ (by simp)]`. Rewrite `v` using `[d1 _ ((min_le_left _ _).trans (by rw [Fin.val_rev]; dsimp only; omega))]`. Simplify using `only [shiftNu, cPair, wtH, hi, dif_pos, Fin.eta] at u v`. Simplify using `only [wtK]`.

Move the coercions through the operations in `at u v`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hj` using `j.2`. Establish `hr` using `j.rev.2`. Establish `u` using `e2 j`.

Establish `v` using `e3 (Fin.rev ⟨j.rev.1, by omega⟩)`. Establish `hp : ¬ (Fin.rev (⟨j.rev.1, by omega⟩ : Fin n)).1 < p`. Rewrite using `[Fin.val_rev]`. Simplify using `only`. Use linear arithmetic over natural numbers and integers.

Rewrite `u` using `[c1 _ (by simp)]`. Rewrite `v` using `[a1 _ ((min_le_left _ _).trans (not_lt.1 hp))]`. Simplify using `only [shiftNu, cPair, wtH, dif_neg hp, Fin.rev_rev, hr, dif_pos, Fin.eta] at u v`. Simplify using `only [wtK]`. Move the coercions through the operations in `at u v`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem weight_eq_wtK (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ)
    (μ : Ix p q → ℚ) (P : Pol p q n 0) (h1 : IsHW (fockAct1 p q n 0) μ P)
    (h2 : P ∈ hwSub (fockAct2 p q n 0) (wtH n ap am))
    (h3 : KilledByLower (fockAct1 p q n 0) P) : μ = wtK n ap am := by
  have hj : P ∈ jointHW μ (wtH n ap am) := by
    refine ⟨⟨h1.2, h2⟩, ⟨fun a b => ?_, fun a b => by simp⟩, fun _ j => j.elim0, fun i => i.elim0⟩
    have := h3 a b
    rw [GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.fockAct1_lower, neg_eq_zero] at this
    exact this
  obtain ⟨α, β, γ, δ, ⟨-, -, -, -, a1, b1, c1, d1, -, -, -, -, e1, e2, e3, -⟩, -⟩ :=
    four_of_joint h1.1 hj
  funext x
  rcases x with i | j
  · have hi := i.2
    have u := e1 i
    have v := e3 ⟨i.1, by omega⟩
    rw [b1 _ (by simp)] at u
    rw [d1 _ ((min_le_left _ _).trans (by rw [Fin.val_rev]; dsimp only; omega))] at v
    simp only [shiftNu, cPair, wtH, hi, dif_pos, Fin.eta] at u v
    simp only [wtK]
    push_cast at u v
    linarith
  · have hj := j.2
    have hr := j.rev.2
    have u := e2 j
    have v := e3 (Fin.rev ⟨j.rev.1, by omega⟩)
    have hp : ¬ (Fin.rev (⟨j.rev.1, by omega⟩ : Fin n)).1 < p := by
      rw [Fin.val_rev]; dsimp only; omega
    rw [c1 _ (by simp)] at u
    rw [a1 _ ((min_le_left _ _).trans (not_lt.1 hp))] at v
    simp only [shiftNu, cPair, wtH, dif_neg hp, Fin.rev_rev, hr, dif_pos, Fin.eta] at u v
    simp only [wtK]
    push_cast at u v
    linarith

end GlobalTheory.HarmonicShape
