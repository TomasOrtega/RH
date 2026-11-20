import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelConjugateTransfer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConjModelTr.exists_conjModelTr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FDiscreteSeriesModelConjugateTransfer.lean&line=283#L283)
-/
theorem _root_.GlobalTheory.T.discrete_series_model_conjugate_transfer : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ (M₁ : DSModel (sgn false V) fun τ => dualPar (S τ)) (κ : SmT M₁ ≃+ SmT M), ModelTr (starRingEnd ℂ) false θ M₁ M κ := by
  first | exact @GlobalTheory.ConjModelTr.exists_conjModelTr | exact GlobalTheory.ConjModelTr.exists_conjModelTr | (intros; apply GlobalTheory.ConjModelTr.exists_conjModelTr <;> assumption)
