import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped Matrix
open Formalism.BasicNotions.TH

namespace GlobalTheory

/- English proof (translation)
Establish `hne : ∀ x : ℝ, (1 - 2 * Complex.I * x) ≠ 0`. Introduce `x h`. Use `congrArg Complex.re h` as an intermediate fact. Simplify using `at this`. Introduce `x y hxy`.

Simplify using `only at hxy`. Rewrite `hxy` using `[div_eq_div_iff (hne x) (hne y)]`. Establish `h2 : ((x : ℂ) - y) * (4 * Complex.I) = 0` using `by linear_combination hxy`. Break down `mul_eq_zero.1 h2 with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h` after adjusting the coercions.

It suffices to derive a contradiction. Use `Complex.I_ne_zero` as an intermediate fact. Apply `this` to reduce the goal to its premises. Take the linear combination `h / 4`.
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
Introduce `m hm`. Assume the negation of the conclusion as `hm0`. Use `set f : ℝ → ℂ := fun x => (1 + 2 * Complex.I * x) / (1 - 2 * Complex.I * x) with hf`. Establish `hn : 0 < m.natAbs` using `Int.natAbs_pos.2 hm0`. Establish `hpow : ∀ x : ℝ, f x ^ m.natAbs = 1`.

Introduce `x`. Establish `h` using `hm x`. Break down `Int.natAbs_eq m with e | e` into its components or cases. Rewrite `h` using `[e, zpow_natCast]`. Conclude with `h`.

Rewrite `h` using `[e, zpow_neg, zpow_natCast, inv_eq_one]`. Conclude with `h`. Set `S : Finset ℂ` to `(Polynomial.nthRoots m.natAbs (1 : ℂ)).toFinset`. Establish `hS : ∀ x : ℝ, f x ∈ S`. Introduce `x`.

Simplify using `only [S, Multiset.mem_toFinset]`. Conclude with `(Polynomial.mem_nthRoots hn).2 (hpow x)`. Establish `: Finite ℝ` using `Finite.of_injective (fun x : ℝ => (⟨f x, hS x⟩ : S)) (by`. Introduce `x y hxy`. Conclude with `cayley_two_injective (congrArg Subtype.val hxy))`.

Conclude with `not_finite ℝ`.
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
