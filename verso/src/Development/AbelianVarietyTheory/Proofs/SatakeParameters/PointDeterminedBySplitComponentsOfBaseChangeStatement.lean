import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointDeterminedBySplitComponentsOfBaseChange
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FPointDeterminedBySplitComponentsOfBaseChange.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.pointDeterminedBySplitComponents_of_baseChange : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.PtOfLoc N A i := by
  first | exact @GlobalTheory.PtOfLocSplit.main | exact GlobalTheory.PtOfLocSplit.main | (intros; apply GlobalTheory.PtOfLocSplit.main <;> assumption)
