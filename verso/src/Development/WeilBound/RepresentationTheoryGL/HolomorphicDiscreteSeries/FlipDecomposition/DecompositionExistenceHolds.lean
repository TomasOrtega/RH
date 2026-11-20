import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.DecompositionUnitaryShift
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.FlipDec
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.FlipDecomposition.OccurrenceOfWalk

noncomputable section

open Finset

namespace PositivityTheory.RgHe.Dec

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem flip_discrete_series_holds : FlipDS := fun m ε lam K _ _ σ =>
  ⟨isDS_of_flip, GlobalTheory.CompanionTheory.NegDS.isDS_flip m K ε lam σ⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem decomposition_existence_holds : DecEx2 := decEx2_of decomposition_le_holds flip_discrete_series_holds flip_decomposition_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem walk : StepL → StepM → Base → Occ := occurrence_of_walk

end PositivityTheory.RgHe.Dec
