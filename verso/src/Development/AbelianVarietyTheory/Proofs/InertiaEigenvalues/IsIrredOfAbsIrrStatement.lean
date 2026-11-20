import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrredOfAbsIrr
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsIrredOfAbsIrr.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.isIrred_of_absIrr : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k), AbsIrrSub ρ ⊤ → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsIrred (matRep ((Units.coeHom _).comp ρ)) := by
  first | exact @GlobalTheory.IrredOfAbsIrred.isIrred_of_absIrrSub | exact GlobalTheory.IrredOfAbsIrred.isIrred_of_absIrrSub | (intros; apply GlobalTheory.IrredOfAbsIrred.isIrred_of_absIrrSub <;> assumption)
