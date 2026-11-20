import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoefInWeilOperatorTranslateAlgebraic
import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FCoefInWeilOperatorTranslateAlgebraic.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.coefIn_weilOperator_translate_algebraic : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (F : VC D N N' → ℂ) (Λ : AddSubgroup (VC D N N')) (p : ℕ) [Fact p.Prime] (y t : VC D N N'), ContDiff ℂ ⊤ F → (∀ s : VC D N N', (∃ a : ℕ, 0 < a ∧ a • s ∈ Λ) → CoefIn D (U D T s F) Qbar) → (∃ a : ℕ, 0 < a ∧ a • t ∈ Λ) → (∃ a : ℕ, 0 < a ∧ a • y ∈ Λ) → (∀ x ∈ Λ, ∀ x' ∈ Λ, ∃ k : ℤ, (Hf D T x x').im = k) → (∃ m : ℤ, qH D T y = m) → CoefIn D (Wop D T p y (U D T t F)) Qbar := by
  first | exact @GlobalTheory.coefIn_Wop_U_translate | exact GlobalTheory.coefIn_Wop_U_translate | (intros; apply GlobalTheory.coefIn_Wop_U_translate <;> assumption)
