import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped Matrix
open Formalism.BasicNotions.TH

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem cayley_two_injective :
    Function.Injective (fun x : ℝ => (1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x)) := by
  have hne : ∀ x : ℝ, (1 - 2 * Complex.I * x) ≠ 0 := by
    intro x h
    have := congrArg Complex.re h
    simp at this
  intro x y hxy
  simp only at hxy
  rw [div_eq_div_iff (hne x) (hne y)] at hxy
  have h2 : ((x : ℂ) - y) * (4 * Complex.I) = 0 := by linear_combination hxy
  rcases mul_eq_zero.1 h2 with h | h
  · exact_mod_cast sub_eq_zero.1 h
  · exfalso; have := Complex.I_ne_zero; apply this; linear_combination h / 4

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem zpow_cayley_two_eq_one_forall :
    ∀ m : ℤ, (∀ x : ℝ, ((1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x)) ^ m = 1) → m = 0 := by
  intro m hm
  by_contra hm0
  set f : ℝ → ℂ := fun x => (1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x) with hf
  have hn : 0 < m.natAbs := Int.natAbs_pos.2 hm0
  have hpow : ∀ x : ℝ, f x ^ m.natAbs = 1 := by
    intro x
    have h := hm x
    rcases Int.natAbs_eq m with e | e
    · rw [e, zpow_natCast] at h; exact h
    · rw [e, zpow_neg, zpow_natCast, inv_eq_one] at h; exact h
  let S : Finset ℂ := (Polynomial.nthRoots m.natAbs (1 : ℂ)).toFinset
  have hS : ∀ x : ℝ, f x ∈ S := by
    intro x
    simp only [S, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots hn).2 (hpow x)
  have : Finite ℝ :=
    Finite.of_injective (fun x : ℝ => (⟨f x, hS x⟩ : S)) (by
      intro x y hxy
      exact cayley_two_injective (congrArg Subtype.val hxy))
  exact not_finite ℝ

end GlobalTheory
