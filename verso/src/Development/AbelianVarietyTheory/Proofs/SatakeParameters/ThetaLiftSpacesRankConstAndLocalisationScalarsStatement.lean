import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftSpacesRankConstAndLocalisationScalars
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RankTw.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FThetaLiftSpacesRankConstAndLocalisationScalars.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.thetaLiftSpaces_rank_const_and_localisation_scalars : ∀ D : D7, Formalism.MainNotions.SumRepresentations.adm8 D → GlobalTheory.NRows.LamUsed D → (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) ∧ ∀ L : SizeData₂ D, Formalism.MainNotions.TwistedPlaces.adm3 L := by
  first | exact @GlobalTheory.RankTw.main | exact GlobalTheory.RankTw.main | (intros; apply GlobalTheory.RankTw.main <;> assumption)
