import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm

open Formalism.REAL Finset

namespace GlobalTheory.CapelliNegT

open Finset in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Simplify using the standard rewrite rules.

Normalize the expressions using the abelian group laws. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), _root_.Formalism.REAL.GlRel E →
      _root_.Formalism.REAL.GlRel (fun a b => -E b a) ∧
        ∀ u : ℂ, _root_.Formalism.REAL.qdet (fun a b => -E b a) u = ((-1 : ℂ) ^ n) • _root_.Formalism.REAL.qdet E ((n : ℂ) - 1 - u) := by
  intro A _ _ n E hE
  refine ⟨?_, fun u => ?_⟩
  · unfold _root_.Formalism.REAL.GlRel at hE ⊢
    intro a b c d
    have h := hE b a d c
    rw [neg_mul_neg, neg_mul_neg, h]
    simp only [@eq_comm _ a d, @eq_comm _ c b]
    split_ifs <;> abel
  · have hrow : ∀ v : ℂ, _root_.Formalism.REAL.qdet E v = _root_.PI.qminorRow E id id v := by
      intro v
      have key : _root_.PI.RowForm := _root_.quantum_minor_row_form
      unfold _root_.PI.RowForm at key
      exact key A n n E hE id id v
    have hM : ∀ (x : ℂ) (a b : Fin n),
        _root_.Formalism.REAL.Tm (fun a b => -E b a) x a b = -_root_.Formalism.REAL.Tm E (-x) b a := by
      intro x a b
      unfold _root_.Formalism.REAL.Tm
      by_cases h : a = b
      · subst h
        simp only [if_true, map_neg]
        abel
      · simp only [h, Ne.symm h, if_false]
        abel
    have hneg : ∀ g : Fin n → A, (List.ofFn fun k => -g k).prod = (-1) ^ n * (List.ofFn g).prod := by
      intro g
      have hl : (List.ofFn fun k => -g k) = (List.ofFn g).map Neg.neg := by
        rw [List.map_ofFn]
        rfl
      rw [hl, List.prod_map_neg, List.length_ofFn]
    have harg : ∀ k : Fin n, -(u - ((k : ℕ) : ℂ)) = (n : ℂ) - 1 - u - n + 1 + ((k : ℕ) : ℂ) := by
      intro k
      ring
    rw [hrow]
    unfold _root_.Formalism.REAL.qdet _root_.Formalism.REAL.qminor _root_.PI.qminorRow
    rw [Algebra.smul_def, map_pow, map_neg, map_one, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hM, hneg, harg, id]
    rw [← mul_assoc, ← mul_assoc, ((Commute.neg_one_right _).pow_right n).eq]

end GlobalTheory.CapelliNegT
