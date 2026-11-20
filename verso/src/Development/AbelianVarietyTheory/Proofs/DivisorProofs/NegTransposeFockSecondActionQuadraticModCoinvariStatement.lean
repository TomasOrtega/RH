import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegTransposeFockSecondActionQuadraticModCoinvari
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HoweR.QuadT.negT_fockAct2_quad` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNegTransposeFockSecondActionQuadraticModCoinvari.lean&line=116#L116)
-/
theorem _root_.GlobalTheory.T.negTranspose_fockSecondAction_quadratic_mod_coinvariants : ∀ (P Q R S : ℕ) (x : ℂ), ∃ α β : ℂ, ∀ a b f, qop (negT (units (fockAct2 P Q R S))) α β a b f ∈ coinv P Q R S x := by
  first | exact @GlobalTheory.HoweR.QuadT.negT_fockAct2_quad | exact GlobalTheory.HoweR.QuadT.negT_fockAct2_quad | (intros; apply GlobalTheory.HoweR.QuadT.negT_fockAct2_quad <;> assumption)
