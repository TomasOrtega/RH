import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IwaPlace.LocSD.isSDAt_latV` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FIsSelfDualLatticeAtPlaceLatticeCompletion.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion : ∀ (D : D7) (S : HSp D) (L : Lat S) (v : Pl D), IsSelfDualC S L → IsSDAt S v (latV S L (· = v)) := by
  first | exact @GlobalTheory.IwaPlace.LocSD.isSDAt_latV | exact GlobalTheory.IwaPlace.LocSD.isSDAt_latV | (intros; apply GlobalTheory.IwaPlace.LocSD.isSDAt_latV <;> assumption)
