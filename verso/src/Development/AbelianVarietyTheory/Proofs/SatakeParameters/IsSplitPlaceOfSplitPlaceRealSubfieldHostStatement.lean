import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceOfSplitPlaceRealSubfieldHost
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FIsSplitPlaceOfSplitPlaceRealSubfieldHost.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.isSplitPlace_of_splitPlace_realSubfield_host : ∀ (D : D7) (s : SplitPlace D.host.E), IsSplitPl D.host s.w := by
  first | exact @GlobalTheory.SplitPlaceConj.isSplitPl_w | exact GlobalTheory.SplitPlaceConj.isSplitPl_w | (intros; apply GlobalTheory.SplitPlaceConj.isSplitPl_w <;> assumption)
