import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BernsteinZelevinskyDerivativeGLnEqTwistedSum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GLm.der_eq_sum` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FBernsteinZelevinskyDerivativeGLnEqTwistedSum.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.bernsteinZelevinskyDerivativeGLn_eq_twisted_sum : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (F : Gn g n → ℂ) (h : Gn g i), i ≤ n → der ψ i F h = ((g : ℂ) ^ (i * (n - i) + (n - i) * (n - i - 1) / 2))⁻¹ * ∑ x : Gn g n, if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0 := by
  first | exact @GlobalTheory.GLm.der_eq_sum | exact GlobalTheory.GLm.der_eq_sum | (intros; apply GlobalTheory.GLm.der_eq_sum <;> assumption)
