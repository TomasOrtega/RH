import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDiscreteSeriesConjugateReverseContragredient
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIsDiscreteSeriesConjugateReverseContragredient.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.isDiscreteSeries_conjugate_reverse_contragredient : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mn n → (H →L[ℂ] H)), IsDS ε lam σ → IsDS (fun a => ε a.rev) (fun a => -lam a.rev) (fun g => σ ((g.map (starRingEnd ℂ)).submatrix Fin.rev Fin.rev)) := by
  first | exact @GlobalTheory.ArchRec.isDS_conj_rev | exact GlobalTheory.ArchRec.isDS_conj_rev | (intros; apply GlobalTheory.ArchRec.isDS_conj_rev <;> assumption)
