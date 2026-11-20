import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatFinitePlaceCompletionLeAleph0
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SBCount.rank_sb_localField_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FRankSchwartzBruhatFinitePlaceCompletionLeAleph0.lean&line=93#L93)
-/
theorem _root_.GlobalTheory.T.rank_schwartzBruhat_finitePlaceCompletion_le_aleph0 : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (κ : Type) [Fintype κ],
    Module.rank ℂ (GlobalTheory.WeilM.SB (κ → Fv F v)) ≤ Cardinal.aleph0 := by
  first | exact @GlobalTheory.SBCount.rank_sb_localField_le | exact GlobalTheory.SBCount.rank_sb_localField_le | (intros; apply GlobalTheory.SBCount.rank_sb_localField_le <;> assumption)
