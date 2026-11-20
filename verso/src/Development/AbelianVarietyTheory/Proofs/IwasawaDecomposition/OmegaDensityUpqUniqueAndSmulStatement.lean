import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDensityUpqUniqueAndSmul
import Formalism.LocalRingCardinality.DataCD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OmegaDensityScale.omegaDensity_unique_and_smul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FOmegaDensityUpqUniqueAndSmul.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.omegaDensity_upq_unique_and_smul : ∀ (P Q : ℕ) (μ : Measure (UpqT P Q)) (c : ENNReal), OmegaDensity μ c → (∀ c', OmegaDensity μ c' → c' = c) ∧ ∀ a : NNReal, OmegaDensity ((a : ENNReal) • μ) (a * c) := by
  first | exact @GlobalTheory.OmegaDensityScale.omegaDensity_unique_and_smul | exact GlobalTheory.OmegaDensityScale.omegaDensity_unique_and_smul | (intros; apply GlobalTheory.OmegaDensityScale.omegaDensity_unique_and_smul <;> assumption)
