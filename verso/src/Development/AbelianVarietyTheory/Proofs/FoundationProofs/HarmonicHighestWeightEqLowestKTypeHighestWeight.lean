import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FockSingularValues
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.JointHarm

namespace GlobalTheory.HarmonicShape

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Apply function extensionality and compare values at an arbitrary argument. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify by unfolding definitions. Use linear arithmetic over natural numbers and integers. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion.

A detailed English derivation is pending.
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
