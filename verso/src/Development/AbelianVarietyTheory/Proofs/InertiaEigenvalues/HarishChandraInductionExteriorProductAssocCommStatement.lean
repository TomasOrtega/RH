import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionExteriorProductAssocComm
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FHarishChandraInductionExteriorProductAssocComm.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.harishChandraInductionExteriorProduct_assoc_comm : ∀ (g : ℕ) [Fact g.Prime] (a b c n : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (γ : Gn g c → ℂ), IsClass α → IsClass β → IsClass γ → (n = a + b + c → hc (a + b) c (hc a b α β (a + b)) γ n = hc a (b + c) α (hc b c β γ (b + c)) n) ∧ (n = a + b → hc a b α β n = hc b a β α n) ∧ (hc 0 a (fun _ => 1) α a = α ∧ hc a 0 α (fun _ => 1) a = α) := by
  first | exact @GlobalTheory.GLq.HcRing.main | exact GlobalTheory.GLq.HcRing.main | (intros; apply GlobalTheory.GLq.HcRing.main <;> assumption)
