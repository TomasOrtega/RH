import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBar

open GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem strictAnti_of_step {N : ℕ} {α : Type} [Preorder α] (f : Fin N → α)
    (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b < f a) : StrictAnti f := by
  cases N with
  | zero => intro a; exact a.elim0
  | succ n =>
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    exact h _ _ (by simp)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Use the polynomial consequences of the given equalities and inequalities. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem divided_strictAnti : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ,
    StrictAnti (W.u1 τ) ∧ StrictAnti (W.u' τ) ∧ StrictAnti (fun i => (W.u1 τ i : ℝ)) := by
  intro ι _ N W H hD τ
  have hT : (4 : ℤ) ≤ W.T := by have := H.h1; omega
  have hh : (0 : ℤ) < W.h0 := by
    obtain ⟨k1, _⟩ := H.h2
    have := H.weightConst_nonneg
    omega
  have step : ∀ a b : Fin N, (b : ℕ) = a + 1 → W.u1 τ b < W.u1 τ a ∧ W.u' τ b < W.u' τ a := by
    intro a b hab
    obtain ⟨g1, g2, _⟩ := divided_gaps ι N W H hD τ a b hab
    by_cases hb : (b : ℕ) = W.p
    · obtain ⟨e1, e2⟩ := g2 hb
      have ha : ¬ ((b : ℕ) < W.p) := by omega
      have ha' : (a : ℕ) < W.p := by omega
      have p1 : 0 < W.u1 τ a - W.u1 τ b := by
        by_contra hc
        push_neg at hc
        nlinarith
      have p2 : 0 < W.u1 τ a - W.u1 τ b - 3 * N := by
        by_contra hc
        push_neg at hc
        nlinarith
      refine ⟨by omega, ?_⟩
      simp only [Wts.u', if_pos ha', if_neg ha]
      omega
    · have e := g1 hb
      have hN : (0 : ℤ) ≤ W.T + W.Dd + 2 + 2 * N := by positivity
      refine ⟨by omega, ?_⟩
      simp only [Wts.u']
      by_cases ha : (a : ℕ) < W.p
      · have hb' : (b : ℕ) < W.p := by omega
        rw [if_pos ha, if_pos hb']; omega
      · have hb' : ¬ (b : ℕ) < W.p := by omega
        rw [if_neg ha, if_neg hb']; omega
  have s1 : StrictAnti (W.u1 τ) := strictAnti_of_step _ fun a b h => (step a b h).1
  exact ⟨s1, strictAnti_of_step _ fun a b h => (step a b h).2,
    (Int.cast_strictMono (R := ℝ)).comp_strictAnti s1⟩

end GlobalTheory.MeanTop
