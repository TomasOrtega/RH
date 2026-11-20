import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteRepsHalfStandardHomModNsmul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HalfStdFin.exists_reps_half_stdHom` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsFiniteRepsHalfStandardHomModNsmul.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.exists_finite_reps_half_standardHom_mod_nsmul : ∀ (D : D7) (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ stdHom S T, IsHalf E₂ u → ∃ r ∈ R, ∃ v ∈ stdHom S T, IsHalf E₂ v ∧ u = r + k • v := by
  first | exact @GlobalTheory.HalfStdFin.exists_reps_half_stdHom | exact GlobalTheory.HalfStdFin.exists_reps_half_stdHom | (intros; apply GlobalTheory.HalfStdFin.exists_reps_half_stdHom <;> assumption)
