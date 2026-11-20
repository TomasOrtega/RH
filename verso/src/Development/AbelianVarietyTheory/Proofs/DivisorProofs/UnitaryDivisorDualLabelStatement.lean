import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDivisorDualLabel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DualDivU.hasDiv_dualLab` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryDivisorDualLabel.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.unitary_divisor_dual_label : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (d : List ℤ) (g : GL (Fin n) L), (∀ x, Valued.v (σ x) = Valued.v x) → d.length = n → g ∈ GU σ n → HasDiv (intL L) d g → HasDiv (intL L) (dualLab d) g := by
  first | exact @GlobalTheory.DualDivU.hasDiv_dualLab | exact GlobalTheory.DualDivU.hasDiv_dualLab | (intros; apply GlobalTheory.DualDivU.hasDiv_dualLab <;> assumption)
