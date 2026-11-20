import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryVolumeEqRankMassAllSignatures
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Glob.vol_eq_massI_all_sig` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FUnitaryVolumeEqRankMassAllSignatures.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.unitary_volume_eq_rank_mass_all_signatures : ∀ D : D7, VolTie D → Conclusion2 D → ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → D.vol W = massI D (P + Q) := by
  first | exact @GlobalTheory.Glob.vol_eq_massI_all_sig | exact GlobalTheory.Glob.vol_eq_massI_all_sig | (intros; apply GlobalTheory.Glob.vol_eq_massI_all_sig <;> assumption)
