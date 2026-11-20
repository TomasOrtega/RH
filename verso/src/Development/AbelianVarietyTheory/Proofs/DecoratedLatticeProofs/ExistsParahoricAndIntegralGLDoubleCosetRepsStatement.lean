import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParahoricAndIntegralGLDoubleCosetReps
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsParahoricAndIntegralGLDoubleCosetReps.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_parahoric_and_integralGL_doubleCosetReps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D], (∀ g : GL (A ⊕ D) k, ∃ R d, IsReps g R d) ∧ ∀ g : GL D k, ∃ R, IsRepsK g R := by
  first | exact @GlobalTheory.ParHeckeReps.exists_reps_both | exact GlobalTheory.ParHeckeReps.exists_reps_both | (intros; apply GlobalTheory.ParHeckeReps.exists_reps_both <;> assumption)
