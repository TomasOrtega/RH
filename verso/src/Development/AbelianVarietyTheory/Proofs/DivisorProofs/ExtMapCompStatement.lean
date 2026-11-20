import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapComp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.ExtFunctor.extMap_comp | exact GlobalTheory.ExtFunctor.extMap_comp | (intros; apply GlobalTheory.ExtFunctor.extMap_comp <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.extMap_comp_extMap : ∀ {m : ℕ} (φ ψ : Matrix (Fin m) (Fin m) ℂ), extMap φ ∘L extMap ψ = extMap (ψ * φ) := by
  first | exact @GlobalTheory.ExtFunctor.extMap_comp | exact GlobalTheory.ExtFunctor.extMap_comp | (intros; apply GlobalTheory.ExtFunctor.extMap_comp <;> assumption)
