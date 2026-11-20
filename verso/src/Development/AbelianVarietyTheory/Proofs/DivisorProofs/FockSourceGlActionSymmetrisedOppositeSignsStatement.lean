import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSourceGlActionSymmetrisedOppositeSigns
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColDerApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFockSourceGlActionSymmetrisedOppositeSigns.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.fockSourceGlActionSymmetrised_opposite_signs : ∀ {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin a) (Fin a) ℂ),
    (∀ i j, ε' i ≠ ε j) →
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' Y = -(GlobalTheory.ColLie.colDer τ Y.transpose : Module.End ℂ (PolF D b a)) - (((b : ℂ) / 2) * Y.trace) • 1 := by
  first | exact @GlobalTheory.FockOpp.fockS_of_opposite | exact GlobalTheory.FockOpp.fockS_of_opposite | (intros; apply GlobalTheory.FockOpp.fockS_of_opposite <;> assumption)
