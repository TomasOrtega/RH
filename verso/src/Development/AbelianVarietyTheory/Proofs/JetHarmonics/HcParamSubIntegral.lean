import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory

/- English proof (translation)
Introduce `n lam lam' h h'`. Use `choose m hm using h.2`. Use `choose m' hm' using h'.2`. Establish `key : ∀ a, lam' a - lam a = ((m' a - m a : ℤ) : ℝ)`. Introduce `a`.

Use `push_cast`. Combine the linear relations using `[hm a, hm' a]`. Use `⟨fun a => m' a - m a, ?_, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Combine the linear relations using `[key a]`.

Unfold `BranchingSupport.n1 l1`. Rewrite using `[Nat.cast_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[key a, Nat.cast_natAbs, Int.cast_abs]`. Introduce `s`.

Unfold `l1`. Conclude with `Finset.single_le_sum (f := fun a => |lam' a - lam a|) (fun a _ => abs_nonneg _) (Finset.mem_univ s)`.
-/
theorem hcParam_sub_integral : ∀ (n : ℕ) (lam lam' : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.IsHCParam lam' → ∃ ν : Fin n → ℤ, lam' = (fun a => lam a + (ν a : ℝ)) ∧ ((BranchingSupport.n1 ν : ℕ) : ℝ) = l1 lam' lam ∧ ∀ s, |lam' s - lam s| ≤ l1 lam' lam := by
  intro n lam lam' h h'
  choose m hm using h.2
  choose m' hm' using h'.2
  have key : ∀ a, lam' a - lam a = ((m' a - m a : ℤ) : ℝ) := by
    intro a
    push_cast
    linarith [hm a, hm' a]
  refine ⟨fun a => m' a - m a, ?_, ?_, ?_⟩
  · funext a
    linarith [key a]
  · unfold BranchingSupport.n1 l1
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [key a, Nat.cast_natAbs, Int.cast_abs]
  · intro s
    unfold l1
    exact Finset.single_le_sum (f := fun a => |lam' a - lam a|) (fun a _ => abs_nonneg _) (Finset.mem_univ s)

end GlobalTheory
