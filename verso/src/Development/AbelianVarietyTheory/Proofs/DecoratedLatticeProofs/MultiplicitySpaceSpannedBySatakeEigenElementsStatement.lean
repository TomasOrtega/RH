import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceSpannedBySatakeEigenElements
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ChainOnto.eigSpan_of_parts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FMultiplicitySpaceSpannedBySatakeEigenElements.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.multiplicity_space_spanned_by_satake_eigen_elements : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → MetEx D → LevFacts D → EigSpan D := by
  first | exact @GlobalTheory.ChainOnto.eigSpan_of_parts | exact GlobalTheory.ChainOnto.eigSpan_of_parts | (intros; apply GlobalTheory.ChainOnto.eigSpan_of_parts <;> assumption)
