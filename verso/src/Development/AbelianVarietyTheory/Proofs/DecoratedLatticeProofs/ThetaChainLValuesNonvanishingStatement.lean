import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLValuesNonvanishing
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FThetaChainLValuesNonvanishing.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.thetaChain_LValues_nonvanishing : ∀ D : D7, ChainLW D := by
  first | exact @GlobalTheory.ChainOnto.chainLW_holds | exact GlobalTheory.ChainOnto.chainLW_holds | (intros; apply GlobalTheory.ChainOnto.chainLW_holds <;> assumption)
