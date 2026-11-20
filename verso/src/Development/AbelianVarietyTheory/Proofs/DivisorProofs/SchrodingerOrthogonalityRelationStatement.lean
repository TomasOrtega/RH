import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerOrthogonalityRelation
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchrodingerOrthogonalityRelation.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.schrodinger_orthogonality_relation : ∀ (n : ℕ) (f g g' : Sch (Fin n)) (x : EuclideanSpace ℝ (Fin n)),
    ∫ w : Fin n ⊕ Fin n → ℝ, starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * rhoFun w ⇑f x =
      (∫ t, f t * starRingEnd ℂ (g t)) * g' x := by
  first | exact @GlobalTheory.MoyalPointwise.moyal_pointwise | exact GlobalTheory.MoyalPointwise.moyal_pointwise | (intros; apply GlobalTheory.MoyalPointwise.moyal_pointwise <;> assumption)
