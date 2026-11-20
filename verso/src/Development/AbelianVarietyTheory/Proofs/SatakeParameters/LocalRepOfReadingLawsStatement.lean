import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalRepOfReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RepOfLocal.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLocalRepOfReadingLaws.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.local_rep_of_reading_laws : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ S : Reading P.T, IsTrue P S → Laws S → ∀ i, RepOfLoc D.nd D.naut i := by
  first | exact @GlobalTheory.RepOfLocal.main | exact GlobalTheory.RepOfLocal.main | (intros; apply GlobalTheory.RepOfLocal.main <;> assumption)
