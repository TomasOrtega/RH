import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

/- English proof (translation)
Unfold `mass`. Rewrite using `[Finset.sum_filter]`.
-/
theorem mass_eq_sum_ite_union (g : ℕ) [Fact g.Prime] (N : ℕ) (A : (ZMod g)[X] → Prop) :
    mass g N A = ∑ f ∈ sqSet g N, if A f then ((torusCard g f : ℝ))⁻¹ else 0 := by
  unfold mass
  rw [Finset.sum_filter]

/- English proof (translation)
Introduce `g _ N`. Establish `hw : ∀ f : (ZMod g)[X], (0 : ℝ) ≤ ((torusCard g f : ℝ))⁻¹` using `fun f => by positivity`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `A B h`. Simplify using `only [mass_eq_sum_ite_union]`.

Use `Finset.sum_le_sum fun f hf => ?_` and prove the remaining obligations. Distinguish the cases in `hA : A f`. Rewrite using `[if_pos hA, if_pos (h f hf hA)]`. Rewrite using `[if_neg hA] split_ifs`. Conclude with `hw f`.

Conclude with `le_rfl`. Introduce `A`. Conclude with `Finset.sum_nonneg fun f _ => hw f`. Introduce `κ s A B h`. Simplify using `only [mass_eq_sum_ite_union]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_le_sum fun f hf => ?_` and prove the remaining obligations. Establish `hn : ∀ i ∈ s, (0 : ℝ) ≤ if B i f then ((torusCard g f : ℝ))⁻¹ else 0`. Introduce `i _`. Use `split_ifs`.

Conclude with `hw f`. Conclude with `le_rfl`. Distinguish the cases in `hA : A f`. Take `⟨i, hi, hB⟩` from `h f hf hA`. Rewrite using `[if_pos hA]`.

Use `Finset.single_le_sum hn hi` as an intermediate fact. Simplify `this` using `only [if_pos hB]`. Rewrite using `[if_neg hA]`. Conclude with `Finset.sum_nonneg hn`. Introduce `A`.

Rewrite using `[mass_eq_sum_ite_union, mass_eq_sum_ite_union, mass_eq_sum_ite_union, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hA : A f <;> simp [hA]`.
-/
theorem mass_union_bounds : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ), (∀ A B : (ZMod g)[X] → Prop, (∀ f ∈ sqSet g N, A f → B f) → mass g N A ≤ mass g N B) ∧ (∀ A, 0 ≤ mass g N A) ∧ (∀ (κ : Type) (s : Finset κ) (A : (ZMod g)[X] → Prop) (B : κ → (ZMod g)[X] → Prop), (∀ f ∈ sqSet g N, A f → ∃ i ∈ s, B i f) → mass g N A ≤ ∑ i ∈ s, mass g N (B i)) ∧ ∀ A : (ZMod g)[X] → Prop, mass g N A + mass g N (fun f => ¬ A f) = mass g N fun _ => True := by
  intro g _ N
  have hw : ∀ f : (ZMod g)[X], (0 : ℝ) ≤ ((torusCard g f : ℝ))⁻¹ := fun f => by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B h
    simp only [mass_eq_sum_ite_union]
    refine Finset.sum_le_sum fun f hf => ?_
    by_cases hA : A f
    · rw [if_pos hA, if_pos (h f hf hA)]
    · rw [if_neg hA]
      split_ifs
      · exact hw f
      · exact le_rfl
  · intro A
    exact Finset.sum_nonneg fun f _ => hw f
  · intro κ s A B h
    simp only [mass_eq_sum_ite_union]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun f hf => ?_
    have hn : ∀ i ∈ s, (0 : ℝ) ≤ if B i f then ((torusCard g f : ℝ))⁻¹ else 0 := by
      intro i _
      split_ifs
      · exact hw f
      · exact le_rfl
    by_cases hA : A f
    · obtain ⟨i, hi, hB⟩ := h f hf hA
      rw [if_pos hA]
      have := Finset.single_le_sum hn hi
      simpa only [if_pos hB] using this
    · rw [if_neg hA]
      exact Finset.sum_nonneg hn
  · intro A
    rw [mass_eq_sum_ite_union, mass_eq_sum_ite_union, mass_eq_sum_ite_union, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases hA : A f <;> simp [hA]

end GlobalTheory.BadShare
