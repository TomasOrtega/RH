import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfOrthogonalSchrodingerGaussian
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzTranslate
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FEqZeroOfOrthogonalSchrodingerGaussian.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.eq_zero_of_orthogonal_schrodinger_gaussian : ∀ (l : Type) [Fintype l] (k : Sch l), (∀ w : l ⊕ l → ℝ, inner ℂ ((rhoSch w (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))).toLp 2 volume) (k.toLp 2 volume) = 0) → k = 0 := by
  first | exact @GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian | exact GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian | (intros; apply GlobalTheory.RealWeil.eq_zero_of_inner_rhoSch_gaussian <;> assumption)
