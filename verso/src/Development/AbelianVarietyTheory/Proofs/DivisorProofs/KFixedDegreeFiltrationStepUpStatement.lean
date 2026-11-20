import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFixedDegreeFiltrationStepUp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKFixedDegreeFiltrationStepUp.lean&line=190#L190)
-/
theorem _root_.GlobalTheory.T.k_fixed_degree_filtration_step_up : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P Q R S : ℕ) (c : ι → ℚ) (m : ℕ)
    (T₀ T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S), T₀ ≠ 0 →
    T₀ ∈ GlobalTheory.KFixIrr.chiPart ι P Q R S c ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S m →
    T ∈ GlobalTheory.KFixIrr.chiPart ι P Q R S c ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S (m + 2) →
    T ∈ GlobalTheory.KFixIrr.degLE ι P Q R S (m + 1) ⊔ Submodule.span ℂ {T' | ∃ (w : ι) (Z : Formalism.BasicNotions.TH.Mat R S),
      ∃ T₁ ∈ GlobalTheory.KFixIrr.chiPart ι P Q R S c ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S m,
        T' = GlobalTheory.RealLift.atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (Formalism.BasicNotions.TH.fockAct2 P Q R S Z) T₁} := by
  first | exact @GlobalTheory.KFixIrr.evenStep_tens | exact GlobalTheory.KFixIrr.evenStep_tens | (intros; apply GlobalTheory.KFixIrr.evenStep_tens <;> assumption)
