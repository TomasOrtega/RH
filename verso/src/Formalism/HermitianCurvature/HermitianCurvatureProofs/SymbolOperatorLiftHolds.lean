import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartEqsOfParts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def liftA {d o : ℕ} (a : (k : Fin (o + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ) (m' : ℕ) :
    (k : Fin (m' + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ :=
  fun k w x => if h : (k : ℕ) ≤ o then a ⟨k, by omega⟩ w x else 0

/- English proof (translation)
Introduce `d S m' O hle hS`. Take `⟨o, a⟩` from `S`. Simplify using `only at hle`. Use `⟨⟨m', liftA a m'⟩, rfl, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i w`.

Express the relevant statement in the definitionally equal form `ContDiffOn ℝ ∞ (liftA a m' i w) O`. Distinguish the cases in `h : (i : ℕ) ≤ o`. Establish `e : liftA a m' i w = a ⟨i, by omega⟩ w` using `funext fun x => dif_pos h`. Rewrite using `[e]`. Conclude with `hS (⟨i, Nat.lt_succ_of_le h⟩ : Fin (o + 1)) w`.

Establish `e : liftA a m' i w = fun _ => 0` using `funext fun x => dif_neg h`. Rewrite using `[e]`. Conclude with `contDiffOn_const`. Introduce `u x`. Simplify using `only [SOp.app]`.

Set `F : ℕ → ℂ` to `fun n => if h : n ≤ o then ∑ w : Fin n → Fin d, a ⟨n, by omega⟩ w x * pdc (List.ofFn w) u x else 0`. Establish `h1 : ∑ k : Fin (m' + 1), ∑ w : Fin k → Fin d, liftA a m' k w x * pdc (List.ofFn w) u x = ∑ k : Fin (m' + 1), F k`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [F, liftA]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Simplify using the standard rewrite rules. Establish `h2 : ∑ k : Fin (o + 1), ∑ w : Fin k → Fin d, a k w x * pdc (List.ofFn w) u x = ∑ k : Fin (o + 1), F k`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [F]`.

Rewrite using `[dif_pos (by omega)]`. Rewrite using `[h1, h2, Fin.sum_univ_eq_sum_range F, Fin.sum_univ_eq_sum_range F]`. Use `symm`. Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `n hn`.

Simplify using `only [Finset.mem_range] at hn ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `n hn hn'`. Simplify using `only [Finset.mem_range] at hn hn'`. Simplify using `only [F]`.

Rewrite using `[dif_neg (by omega)]`. Introduce `x ξ`. Simplify using `only [SOp.symb]`. Distinguish the cases in `h : o = m'`. Substitute `h` using the available equality.

Rewrite using `[if_pos rfl]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `only [liftA]`. Rewrite using `[dif_pos (by simp)]`. Rewrite using `[if_neg h]`.

Use `Finset.sum_eq_zero fun w _ => ?_` and prove the remaining obligations. Simplify using `only [liftA]`. Rewrite using `[dif_neg (by simp; omega)]`. Simplify using the standard rewrite rules.
-/
theorem symbol_operator_lift_holds : SOpLift := by
  intro d S m' O hle hS
  obtain ⟨o, a⟩ := S
  simp only at hle
  refine ⟨⟨m', liftA a m'⟩, rfl, ?_, ?_, ?_⟩
  · intro i w
    change ContDiffOn ℝ ∞ (liftA a m' i w) O
    by_cases h : (i : ℕ) ≤ o
    · have e : liftA a m' i w = a ⟨i, by omega⟩ w := funext fun x => dif_pos h
      rw [e]
      exact hS (⟨i, Nat.lt_succ_of_le h⟩ : Fin (o + 1)) w
    · have e : liftA a m' i w = fun _ => 0 := funext fun x => dif_neg h
      rw [e]
      exact contDiffOn_const
  · intro u x
    simp only [SOp.app]
    let F : ℕ → ℂ := fun n =>
      if h : n ≤ o then ∑ w : Fin n → Fin d, a ⟨n, by omega⟩ w x * pdc (List.ofFn w) u x else 0
    have h1 : ∑ k : Fin (m' + 1), ∑ w : Fin k → Fin d, liftA a m' k w x * pdc (List.ofFn w) u x =
        ∑ k : Fin (m' + 1), F k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [F, liftA]
      split_ifs with h
      · rfl
      · simp
    have h2 : ∑ k : Fin (o + 1), ∑ w : Fin k → Fin d, a k w x * pdc (List.ofFn w) u x =
        ∑ k : Fin (o + 1), F k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [F]
      rw [dif_pos (by omega)]
    rw [h1, h2, Fin.sum_univ_eq_sum_range F, Fin.sum_univ_eq_sum_range F]
    symm
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_range] at hn ⊢
      omega
    · intro n hn hn'
      simp only [Finset.mem_range] at hn hn'
      simp only [F]
      rw [dif_neg (by omega)]
  · intro x ξ
    simp only [SOp.symb]
    by_cases h : o = m'
    · subst h
      rw [if_pos rfl]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [liftA]
      rw [dif_pos (by simp)]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun w _ => ?_
      simp only [liftA]
      rw [dif_neg (by simp; omega)]
      simp

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
