import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatAdicCompletionPiLeAleph0
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FRankSchwartzBruhatAdicCompletionPiLeAleph0.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.rank_schwartzBruhat_adicCompletion_pi_le_aleph0 : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : HeightOneSpectrum (𝓞 F)),
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → v.adicCompletion F)) ≤ Cardinal.aleph0 := by
  first | exact @GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le | exact GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le | (intros; apply GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le <;> assumption)
