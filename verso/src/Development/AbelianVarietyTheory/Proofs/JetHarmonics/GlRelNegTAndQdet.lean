import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm

open Formalism.REAL Finset

namespace GlobalTheory.CapelliNegT

open Finset in

/- English proof (translation)
Introduce `A _ _ n E hE`. Use `⟨?_, fun u => ?_⟩` and prove the remaining obligations. Unfold `_root_.Formalism.REAL.GlRel at hE ⊢`. Introduce `a b c d`. Establish `h` using `hE b a d c`.

Rewrite using `[neg_mul_neg, neg_mul_neg, h]`. Simplify using `only [@eq_comm _ a d, @eq_comm _ c b]`. Apply the tactic sequence `split_ifs <;> abel`. Establish `hrow : ∀ v : ℂ, _root_.Formalism.REAL.qdet E v = _root_.PI.qminorRow E id id v`. Introduce `v`.

Establish `key : _root_.PI.RowForm` using `_root_.quantum_minor_row_form`. Unfold `_root_.PI.RowForm at key`. Conclude with `key A n n E hE id id v`. Establish `hM : ∀ (x : ℂ) (a b : Fin n), _root_.Formalism.REAL.Tm (fun a b => -E b a) x a b = -_root_.Formalism.REAL.Tm E (-x) b a`. Introduce `x a b`.

Unfold `_root_.Formalism.REAL.Tm`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using `only [if_true, map_neg]`. Normalize the expressions using the abelian group laws.

Simplify using `only [h, Ne.symm h, if_false]`. Normalize the expressions using the abelian group laws. Establish `hneg : ∀ g : Fin n → A, (List.ofFn fun k => -g k).prod = (-1) ^ n * (List.ofFn g).prod`. Introduce `g`. Establish `hl : (List.ofFn fun k => -g k) = (List.ofFn g).map Neg.neg`.

Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression. Rewrite using `[hl, List.prod_map_neg, List.length_ofFn]`. Establish `harg : ∀ k : Fin n, -(u - ((k : ℕ) : ℂ)) = (n : ℂ) - 1 - u - n + 1 + ((k : ℕ) : ℂ)`. Introduce `k`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hrow]`. Unfold `_root_.Formalism.REAL.qdet _root_.Formalism.REAL.qminor _root_.PI.qminorRow`. Rewrite using `[Algebra.smul_def, map_pow, map_neg, map_one, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Simplify using `only [hM, hneg, harg, id]`. Rewrite using `[← mul_assoc, ← mul_assoc, ((Commute.neg_one_right _).pow_right n).eq]`.
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
