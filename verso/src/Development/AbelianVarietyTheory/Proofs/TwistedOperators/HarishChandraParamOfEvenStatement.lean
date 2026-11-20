import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarishChandraParamOfEven
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
open Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FHarishChandraParamOfEven.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.harish_chandra_param_of_even : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, Even G.k → Even G.m → n + 1 = G.k + G.m → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → Formalism.QuantumDeterminants.IsHCParam lam ∧ Formalism.QuantumDeterminants.IsHCParam mu := by
  first | exact @GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0 | exact GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0 | (intros; apply GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0 <;> assumption)
