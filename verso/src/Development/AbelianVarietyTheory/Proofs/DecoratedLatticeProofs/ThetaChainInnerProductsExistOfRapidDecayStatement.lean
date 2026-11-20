import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainInnerProductsExistOfRapidDecay
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ChainMetric.metEx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FThetaChainInnerProductsExistOfRapidDecay.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.thetaChainInnerProductsExist_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D := by
  first | exact @GlobalTheory.ChainMetric.metEx | exact GlobalTheory.ChainMetric.metEx | (intros; apply GlobalTheory.ChainMetric.metEx <;> assumption)
