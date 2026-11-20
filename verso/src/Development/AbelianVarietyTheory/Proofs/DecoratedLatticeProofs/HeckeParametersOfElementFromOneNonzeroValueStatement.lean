import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeParametersOfElementFromOneNonzeroValue
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ChainOnto.parOfVal_of_parts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FHeckeParametersOfElementFromOneNonzeroValue.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.hecke_parameters_of_element_from_one_nonzero_value : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → LevFacts D → ParOfVal D := by
  first | exact @GlobalTheory.ChainOnto.parOfVal_of_parts | exact GlobalTheory.ChainOnto.parOfVal_of_parts | (intros; apply GlobalTheory.ChainOnto.parOfVal_of_parts <;> assumption)
