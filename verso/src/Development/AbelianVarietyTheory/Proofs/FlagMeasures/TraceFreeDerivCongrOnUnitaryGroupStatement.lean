import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceFreeDerivCongrOnUnitaryGroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FTraceFreeDerivCongrOnUnitaryGroup.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.traceFreeDeriv_congr_on_unitaryGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (G₁ G₂ : Matrix (Fin n) (Fin n) ℂ → ℂ) (a b : Fin n), (∀ g ∈ SUset ε, G₁ g = G₂ g) → ∀ g ∈ SUset ε, Ec ε (E0 a b) G₁ g = Ec ε (E0 a b) G₂ g := by
  first | exact @GlobalTheory.DSSU.Local.matrix_unit_action_congr | exact GlobalTheory.DSSU.Local.matrix_unit_action_congr | (intros; apply GlobalTheory.DSSU.Local.matrix_unit_action_congr <;> assumption)
