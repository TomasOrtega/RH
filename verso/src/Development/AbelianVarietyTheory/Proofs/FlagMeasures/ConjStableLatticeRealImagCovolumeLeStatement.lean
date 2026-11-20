import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjStableLatticeRealImagCovolumeLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ReImLattice.real_imag_covolume_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FConjStableLatticeRealImagCovolumeLe.lean&line=135#L135)
-/
theorem _root_.GlobalTheory.T.conjStable_lattice_real_imag_covolume_le : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (L : Submodule ℤ (ι → κ → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L], (∀ z ∈ L, (fun v i => starRingEnd ℂ (z v i)) ∈ L) → ∀ A B : Submodule ℤ (ι → κ → ℝ), (∀ y, y ∈ A ↔ (fun v i => (y v i : ℂ)) ∈ L) → (∀ y, y ∈ B ↔ (fun v i => Complex.I * (y v i : ℂ)) ∈ L) → (∃ _ : DiscreteTopology A, IsZLattice ℝ A) ∧ (∃ _ : DiscreteTopology B, IsZLattice ℝ B) ∧ ZLattice.covolume A volume * ZLattice.covolume B volume ≤ 2 ^ (Fintype.card ι * Fintype.card κ) * ZLattice.covolume L volume := by
  first | exact @GlobalTheory.ReImLattice.real_imag_covolume_le | exact GlobalTheory.ReImLattice.real_imag_covolume_le | (intros; apply GlobalTheory.ReImLattice.real_imag_covolume_le <;> assumption)
