import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirLtAddRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealLift.casK_lt_of_isHarmVec_addRoot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCasimirLtAddRoot.lean&line=413#L413)
-/
theorem _root_.GlobalTheory.T.casimir_lt_add_root : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ a b : Formalism.BasicNotions.TH.Ix R S, ¬ Formalism.BasicNotions.TH.sameBlock a b → ∀ f : Formalism.BasicNotions.TH.Pol P Q R S, GlobalTheory.RealLift.IsHarmVec ((κ : ℚ) / 2) (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) f → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) < GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) := by
  first | exact @GlobalTheory.RealLift.casK_lt_of_isHarmVec_addRoot | exact GlobalTheory.RealLift.casK_lt_of_isHarmVec_addRoot | (intros; apply GlobalTheory.RealLift.casK_lt_of_isHarmVec_addRoot <;> assumption)
