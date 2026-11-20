import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZlatticeCovolumeEqOfCoprimeScalars
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FZlatticeCovolumeEqOfCoprimeScalars.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.zlattice_covolume_eq_of_coprime_scalars : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (A B : Submodule ℤ (ι → κ → ℝ)) [DiscreteTopology A] [IsZLattice ℝ A] [DiscreteTopology B] [IsZLattice ℝ B], (∀ p : ℕ, p.Prime → ∃ (d : ι → ℝ) (N : ℕ), ¬ p ∣ N ∧ ∏ v, d v ^ 2 = N ∧ (∀ y ∈ A, (fun v i => d v * y v i) ∈ B) ∧ ∀ y ∈ B, (fun v i => d v * y v i) ∈ A) → ZLattice.covolume A volume = ZLattice.covolume B volume := by
  first | exact @GlobalTheory.CovScal.covolume_eq_of_scalars | exact GlobalTheory.CovScal.covolume_eq_of_scalars | (intros; apply GlobalTheory.CovScal.covolume_eq_of_scalars <;> assumption)
