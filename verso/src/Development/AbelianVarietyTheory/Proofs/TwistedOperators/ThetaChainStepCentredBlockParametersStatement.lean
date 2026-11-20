import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepCentredBlockParameters
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ArchRec.ParChain.parChain` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FThetaChainStepCentredBlockParameters.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.thetaChainStep_centred_block_parameters : ∀ (D : D7) (k : Fin D.R.m) (τ : D.what₂.Tau), ∃ al be ga de : List ℚ, Centred D al be ga de ∧ parA (Ptw D) k τ = signed (al ++ be) (ga ++ de) (alT D k τ) ∧ parA (Ptw D) (k + 1) τ = signed (al ++ block D.R.t ++ de) (ga ++ be) (alS D k τ) := by
  first | exact @GlobalTheory.ArchRec.ParChain.parChain | exact GlobalTheory.ArchRec.ParChain.parChain | (intros; apply GlobalTheory.ArchRec.ParChain.parChain <;> assumption)
