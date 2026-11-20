import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjFB

namespace GlobalTheory.ScalarStatement

open Formalism.L2.FormalSeriesBounds

/- English proof (translation)
Introduce `d1 C _ V ι S s h`. Establish `h' : ∀ i, ∃ K : ℝ, i ∈ S → ∀ n, Formalism.L2.FormalSeriesBounds.VF.Ge V K (s i n)`. Introduce `i`. Distinguish the cases in `hi : i ∈ S`. Take `⟨K, hK⟩` from `h i hi`.

Conclude with `⟨K, fun _ => hK⟩`. Conclude with `⟨0, fun h => absurd h hi⟩`. Use `choose K hK using h'`. Use `⟨-(∑ i ∈ S, |K i|), fun n => ?_⟩` and prove the remaining obligations. Use `Formalism.L2.FormalSeriesBounds.VF.Ge.sum fun i hi => (hK i hi n).mono ?_` and prove the remaining obligations.

Establish `h1 : |K i| ≤ ∑ j ∈ S, |K j|` using `Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _) hi`. Establish `h2 : -|K i| ≤ K i` using `neg_abs_le _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main : (let d1 : {C : Type} → [inst : Field C] → Formalism.L2.FormalSeriesBounds.VF C → (ℕ → C) → Prop := @(fun {C : Type} [Field C] (V : Formalism.L2.FormalSeriesBounds.VF C) (s : ℕ → C) ↦ ∃ (K : ℝ), ∀ (n : ℕ), Formalism.L2.FormalSeriesBounds.VF.Ge V K (s n)); ∀ {C : Type} [inst : Field C] {V : Formalism.L2.FormalSeriesBounds.VF C} {ι : Type} (S : Finset ι) {s : ι → ℕ → C}, (∀ i ∈ S, d1 V (s i)) → d1 V fun (n : ℕ) ↦ ∑ i ∈ S, s i n) := by
  intro d1 C _ V ι S s h
  classical
  have h' : ∀ i, ∃ K : ℝ, i ∈ S → ∀ n, Formalism.L2.FormalSeriesBounds.VF.Ge V K (s i n) := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨K, hK⟩ := h i hi
      exact ⟨K, fun _ => hK⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose K hK using h'
  refine ⟨-(∑ i ∈ S, |K i|), fun n => ?_⟩
  refine Formalism.L2.FormalSeriesBounds.VF.Ge.sum fun i hi => (hK i hi n).mono ?_
  have h1 : |K i| ≤ ∑ j ∈ S, |K j| :=
    Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _) hi
  have h2 : -|K i| ≤ K i := neg_abs_le _
  linarith

end GlobalTheory.ScalarStatement
