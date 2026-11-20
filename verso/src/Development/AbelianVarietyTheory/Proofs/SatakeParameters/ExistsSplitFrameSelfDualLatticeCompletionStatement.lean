import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitFrameSelfDualLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SplitFrame.exists_frame` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsSplitFrameSelfDualLatticeCompletion.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.exists_splitFrame_selfDualLattice_completion : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ V : HSp D, ∃ β : GL (Fin V.rank) (Fv D.host.F v), Frame V e π β := by
  first | exact @GlobalTheory.SplitFrame.exists_frame | exact GlobalTheory.SplitFrame.exists_frame | (intros; apply GlobalTheory.SplitFrame.exists_frame <;> assumption)
