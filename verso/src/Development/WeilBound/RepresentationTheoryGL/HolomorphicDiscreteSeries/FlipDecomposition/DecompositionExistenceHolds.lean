import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.DecompositionUnitaryShift
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.FlipDec
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.OccurrenceOfWalk

noncomputable section

open Finset

namespace PositivityTheory.RgHe.Dec

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition

/- English proof (translation)
Introduce `m ε lam K _ _ σ` and use `⟨isDS_of_flip, GlobalTheory.CompanionTheory.NegDS.isDS_flip m K ε lam σ⟩`.
-/
theorem flip_discrete_series_holds : FlipDS := fun m ε lam K _ _ σ =>
  ⟨isDS_of_flip, GlobalTheory.CompanionTheory.NegDS.isDS_flip m K ε lam σ⟩

/- English proof (translation)
Introduce `m ε lam H _ _ π hf ht hp hds hgap`. Distinguish the cases in `hle : #{a : Fin m | ε a = false} ≤ #{a : Fin m | ε a = true}`. Take `⟨X, hX⟩` from `h1 m ε lam H π hf hle hp hds hgap`. Conclude with `⟨X, hX⟩`. Establish `hds' : IsDS (fun a : Fin m => !ε a) lam π` using `(h2 m ε lam H π).2 hds`.

Establish `hf' : ∃ a : Fin m, (!ε a) = false`. Take `⟨a, ha⟩` from `ht`. Conclude with `⟨a, by simp [ha]⟩`. Establish `hle' : #{a : Fin m | (!ε a) = false} ≤ #{a : Fin m | (!ε a) = true}`. Simplify using `only [Bool.not_eq_false', Bool.not_eq_true']`.

Use linear arithmetic over natural numbers and integers. Establish `hgap' : Formalism.QuantumDeterminants.GapAtLeast (fun a : Fin m => !ε a) lam (200 * (m : ℝ) ^ 3)`. Introduce `a b hab`. Apply `hgap a b` to reduce the goal to its premises. Introduce `h`.

Apply `hab` to reduce the goal to its premises. Simplify using `[h]`. Take `⟨X, hX⟩` from `h1 m (fun a => !ε a) lam H π hf' hle' hp hds' hgap'`. Conclude with `h3 m ε lam H π X hX`.
-/
theorem decEx2_of (h1 : DecLe) (h2 : FlipDS) (h3 : FlipDec) : DecEx2 := by
  intro m ε lam H _ _ π hf ht hp hds hgap
  by_cases hle : #{a : Fin m | ε a = false} ≤ #{a : Fin m | ε a = true}
  · obtain ⟨X, hX⟩ := h1 m ε lam H π hf hle hp hds hgap
    exact ⟨X, hX⟩
  · have hds' : IsDS (fun a : Fin m => !ε a) lam π := (h2 m ε lam H π).2 hds
    have hf' : ∃ a : Fin m, (!ε a) = false := by
      obtain ⟨a, ha⟩ := ht
      exact ⟨a, by simp [ha]⟩
    have hle' : #{a : Fin m | (!ε a) = false} ≤ #{a : Fin m | (!ε a) = true} := by
      simp only [Bool.not_eq_false', Bool.not_eq_true']
      omega
    have hgap' : Formalism.QuantumDeterminants.GapAtLeast (fun a : Fin m => !ε a) lam (200 * (m : ℝ) ^ 3) := by
      intro a b hab
      apply hgap a b
      intro h
      apply hab
      simp [h]
    obtain ⟨X, hX⟩ := h1 m (fun a => !ε a) lam H π hf' hle' hp hds' hgap'
    exact h3 m ε lam H π X hX

/- English proof (translation)
The claim follows from `decEx2_of decomposition_le_holds flip_discrete_series_holds flip_decomposition_holds`.
-/
theorem decomposition_existence_holds : DecEx2 := decEx2_of decomposition_le_holds flip_discrete_series_holds flip_decomposition_holds

/- English proof (translation)
The claim follows from `occurrence_of_walk`.
-/
theorem walk : StepL → StepM → Base → Occ := occurrence_of_walk

end PositivityTheory.RgHe.Dec
