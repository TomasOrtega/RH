import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm Formalism.DegreeFormula

namespace GlobalTheory.FlagForm

/- English proof (translation)
Establish `h1 : toForm (pLow j τ 1 : Pol ι N) = ∑ i : Fin N, if (i : ℕ) < j then rootForm (τ, i) else 0`. Simplify using `only [toForm, pLow, map_sum, Finset.sum_filter, pow_one]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [aeval_X]`. Establish `h2 : toForm (pLow j τ 1 : Pol ι N) = (∑ a : Fin N, ∑ b : Fin N, if a < b ∧ (b : ℕ) < j then X (τ, a, b) else 0) - ∑ a : Fin N, ∑ b : Fin N, if a < b ∧ (a : ℕ) < j then X (τ, a, b) else 0`.

Rewrite using `[h1]`. Simplify using `only [rootForm]`. Establish `: ∀ i : Fin N, (if (i : ℕ) < j then (∑ a : Fin N, (if a < i then (X (τ, a, i) : FormPol ι N) else 0) - ∑ b : Fin N, (if i < b then X (τ, i, b) else 0)) else 0) = (∑ a : Fin N, if a < i ∧ (i : ℕ) < j then X (τ, a, i) else 0) - ∑ b : Fin N, if i < b ∧ (i : ℕ) < j then X (τ, i, b) e …`. Introduce `i`. Use `split_ifs with hi`.

Simplify using `[hi]`. Simplify using `[hi]`. Rewrite using `[Finset.sum_congr rfl (fun i _ => this i), Finset.sum_sub_distrib, Finset.sum_comm]`. Rewrite using `[h2]`. Simplify using `only [bcForm, blkForm]`.

Rewrite using `[eq_sub_iff_add_eq, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Establish `hab : ((a : Fin N) < b) ↔ (a : ℕ) < b` using `Fin.lt_iff_val_lt_val`.

Apply the tactic sequence `by_cases h : a < b <;> by_cases hb : (b : ℕ) < j <;> by_cases ha : (a : ℕ) < j <;>`. Apply the tactic sequence `simp [h, hb, ha] <;> omega`.
-/
theorem bcForm_eq_blkForm_sub_toForm_pLow (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ) (τ : ι) :
    (bcForm τ : FormPol ι N) = blkForm j τ - toForm (pLow j τ 1 : Pol ι N) := by
  have h1 : toForm (pLow j τ 1 : Pol ι N) =
      ∑ i : Fin N, if (i : ℕ) < j then rootForm (τ, i) else 0 := by
    simp only [toForm, pLow, map_sum, Finset.sum_filter, pow_one]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp [aeval_X]
  have h2 : toForm (pLow j τ 1 : Pol ι N) =
      (∑ a : Fin N, ∑ b : Fin N, if a < b ∧ (b : ℕ) < j then X (τ, a, b) else 0) -
      ∑ a : Fin N, ∑ b : Fin N, if a < b ∧ (a : ℕ) < j then X (τ, a, b) else 0 := by
    rw [h1]
    simp only [rootForm]
    have : ∀ i : Fin N, (if (i : ℕ) < j then
        (∑ a : Fin N, (if a < i then (X (τ, a, i) : FormPol ι N) else 0) -
          ∑ b : Fin N, (if i < b then X (τ, i, b) else 0)) else 0) =
        (∑ a : Fin N, if a < i ∧ (i : ℕ) < j then X (τ, a, i) else 0) -
          ∑ b : Fin N, if i < b ∧ (i : ℕ) < j then X (τ, i, b) else 0 := by
      intro i
      split_ifs with hi
      · simp [hi]
      · simp [hi]
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_sub_distrib, Finset.sum_comm]
  rw [h2]
  simp only [bcForm, blkForm]
  rw [eq_sub_iff_add_eq, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hab : ((a : Fin N) < b) ↔ (a : ℕ) < b := Fin.lt_iff_val_lt_val
  by_cases h : a < b <;> by_cases hb : (b : ℕ) < j <;> by_cases ha : (a : ℕ) < j <;>
    simp [h, hb, ha] <;> omega

end GlobalTheory.FlagForm
