import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height

open Matrix GroundTheory.Automorphic.AutomorphicForm

namespace Ad3.GA.Gr

def SumBd (E : Type*) [NormedField E] (c : ℝ) : Prop :=
  ∀ (ι : Type) (s : Finset ι) (f : ι → E) (r : ℝ), s.card ≤ 6 → 0 ≤ r → (∀ i ∈ s, ‖f i‖ ≤ r) →
    ‖∑ i ∈ s, f i‖ ≤ c * r

variable {E : Type*} [NormedField E] {c : ℝ}

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `hc (Equiv.Perm (Fin 3)) Finset.univ _ (m ^ 3) (by rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]; decide) (by positivity) fun σ _ => ?_` and prove the remaining obligations. Establish `hp : ‖∏ i, M (σ i) i‖ ≤ m ^ 3`. Rewrite using `[norm_prod]`. Combine the equalities or inequalities in the displayed calculation.

Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]`. Simplify using `using hp`. Simplify using `using hp`.
-/
theorem SumBd.det_le (hc : SumBd E c) {M : Matrix (Fin 3) (Fin 3) E} {m : ℝ} (hm : 0 ≤ m)
    (hM : ∀ i j, ‖M i j‖ ≤ m) : ‖M.det‖ ≤ c * m ^ 3 := by
  rw [Matrix.det_apply]
  refine hc (Equiv.Perm (Fin 3)) Finset.univ _ (m ^ 3)
    (by rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]; decide) (by positivity)
    fun σ _ => ?_
  have hp : ‖∏ i, M (σ i) i‖ ≤ m ^ 3 := by
    rw [norm_prod]
    calc ∏ i, ‖M (σ i) i‖ ≤ ∏ _i : Fin 3, m :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hM _ _
      _ = m ^ 3 := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · simpa using hp
  · simpa using hp

end Ad3.GA.Gr
