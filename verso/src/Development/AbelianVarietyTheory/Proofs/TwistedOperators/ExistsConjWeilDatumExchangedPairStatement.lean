import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsConjWeilDatumExchangedPair.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.exists_conj_weilDatum_exchangedPair : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : WRep S T), IsWeilDatumO ψ S T χS χT ω → ∃ ω' : WRep T S, IsWeilDatumO ψ T S χT χS ω' ∧ ∀ (g : GA D S) (h : GA D T) (f : WO S T → ℂ), ω' (h, g) (dag S T f) = dag S T (ω (g, h) f) := by
  first | exact @GlobalTheory.WeilConj.exists_conj_weilDatum | exact GlobalTheory.WeilConj.exists_conj_weilDatum | (intros; apply GlobalTheory.WeilConj.exists_conj_weilDatum <;> assumption)
