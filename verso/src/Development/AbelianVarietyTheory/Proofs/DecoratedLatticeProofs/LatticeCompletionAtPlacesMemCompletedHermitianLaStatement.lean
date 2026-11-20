import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLa
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatVHat.latV_mem_hatL` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FLatticeCompletionAtPlacesMemCompletedHermitianLa.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.latticeCompletionAtPlaces_mem_completedHermitianLattice : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D), y ∈ latV S L P → (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L := by
  first | exact @GlobalTheory.LatVHat.latV_mem_hatL | exact GlobalTheory.LatVHat.latV_mem_hatL | (intros; apply GlobalTheory.LatVHat.latV_mem_hatL <;> assumption)
