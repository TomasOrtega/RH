import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayerParametersAdmissible
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.Top.LayOfCore.lay_of_core` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsLayerParametersAdmissible.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.exists_layer_sizeData : Ev fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T), StandardLattice.VolumeEqMass₂ X.toD7 → ∃ Y : Lay X.toD7, layObj Y = c.O ∧ Over X.toD7 K.P K.Lv ∧ RecOK K.s K.C K.cD X.toD7 ∧ LedOK K.s K.C K.cD K.ch Y K.a K.b ∧ DQ.TupUsedAt X.toD7 := by
  first | exact @GlobalTheory.Mem.Top.LayOfCore.lay_of_core | exact GlobalTheory.Mem.Top.LayOfCore.lay_of_core | (intros; apply GlobalTheory.Mem.Top.LayOfCore.lay_of_core <;> assumption)
