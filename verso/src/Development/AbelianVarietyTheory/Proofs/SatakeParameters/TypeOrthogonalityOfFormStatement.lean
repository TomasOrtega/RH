import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeOrthogonalityOfForm
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaExh.typeOrth_of_pin` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FTypeOrthogonalityOfForm.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.type_orthogonality_of_form : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ i : D.nd.Loc, MtForm D P.M i → GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i := by
  first | exact @GlobalTheory.ThetaExh.typeOrth_of_pin | exact GlobalTheory.ThetaExh.typeOrth_of_pin | (intros; apply GlobalTheory.ThetaExh.typeOrth_of_pin <;> assumption)
