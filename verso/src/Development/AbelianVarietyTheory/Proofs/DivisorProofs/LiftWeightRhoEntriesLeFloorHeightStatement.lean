import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoEntriesLeFloorHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLiftWeightRhoEntriesLeFloorHeight.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.liftWeightRho_entries_le_floor_height : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (P5 : Formalism.BasicNotions.ParameterChoice' D L) (j : Fin D.R.m) (τ : D.what₂.Tau), (GlobalTheory.ExpTie.parOf L j).Large → GlobalTheory.ExpTie.Lift.ValsAt L j τ → ∀ a, a < (GlobalTheory.ExpTie.parOf L j).Nr → (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (Formalism.CohomologicalDescent.ShortWeightBounds.h0 (GlobalTheory.ExpTie.parOf L j) : ℤ) := by
  first | exact @GlobalTheory.ExpTie.Lift.wts_U_le_h0_of_large | exact GlobalTheory.ExpTie.Lift.wts_U_le_h0_of_large | (intros; apply GlobalTheory.ExpTie.Lift.wts_U_le_h0_of_large <;> assumption)
