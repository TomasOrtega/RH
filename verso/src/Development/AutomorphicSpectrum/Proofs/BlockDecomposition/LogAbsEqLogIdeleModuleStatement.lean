import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsEqLogIdeleModule
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLogAbsEqLogIdeleModule.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.log_abs_eq_log_idele_module : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (s : (Ad E)ˣ), logAbs (s : Ad E) = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.logAbs_eq_log_ideleModule | exact GlobalTheory.CompanionTheory.TorusCh.logAbs_eq_log_ideleModule | (intros; apply GlobalTheory.CompanionTheory.TorusCh.logAbs_eq_log_ideleModule <;> assumption)
