import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalPointThetaExhaustion
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLocalPointThetaExhaustion.lean&line=168#L168)
-/
theorem _root_.GlobalTheory.T.local_point_theta_exhaustion : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ i, GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  first | exact @GlobalTheory.PtLocalPin.main | exact GlobalTheory.PtLocalPin.main | (intros; apply GlobalTheory.PtLocalPin.main <;> assumption)
