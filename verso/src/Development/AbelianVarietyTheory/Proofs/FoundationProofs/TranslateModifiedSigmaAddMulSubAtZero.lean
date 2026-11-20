import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

/- English proof (translation)
Introduce `Λ hΛ P Q hP hQ`. Establish `hlaw` using `(GlobalTheory.OddTheta.sgStar_laws Λ hΛ).2.2.2.1 P Q hP hQ`. Establish `hσ : sgStar Λ (P + Q) * sgStar Λ (P - Q) = (wpF Λ Q - wpF Λ P) * sgStar Λ P ^ 2 * sgStar Λ Q ^ 2`. Take the linear combination `hlaw`. Simplify using `only [U1, zero_add, mul_zero, zero_mul, zero_div, zero_sub]`.

Establish `hexp : ∀ x : ℂ, Complex.exp x ^ 2 = Complex.exp (2 * x)`. Introduce `x`. Rewrite using `[← Complex.exp_nat_mul]`. Evaluate the numerical expressions. Establish `key : Complex.exp (-(↑Real.pi * (P + Q) * (starRingEnd ℂ) (P + Q) / (2 * ↑(area Λ)))) * Complex.exp (-(↑Real.pi * (P - Q) * (starRingEnd ℂ) (P - Q) / (2 * ↑(area Λ)))) = Complex.exp (-(↑Real.pi * P * (starRingEnd ℂ) P / (2 * ↑(area Λ)))) ^ 2 * Complex.exp (-(↑Real.pi * Q * (starR …`.

Rewrite using `[hexp, hexp, ← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`. Simplify using `only [map_add, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.
-/
theorem translate_modifiedSigma_add_mul_sub_at_zero :
    ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P Q : ℂ, P ∉ Λ → Q ∉ Λ →
      U1 Λ (P + Q) (sgStar Λ) 0 * U1 Λ (P - Q) (sgStar Λ) 0 =
        (wpF Λ Q - wpF Λ P) * U1 Λ P (sgStar Λ) 0 ^ 2 * U1 Λ Q (sgStar Λ) 0 ^ 2 := by
  intro Λ hΛ P Q hP hQ
  have hlaw := (GlobalTheory.OddTheta.sgStar_laws Λ hΛ).2.2.2.1 P Q hP hQ
  have hσ : sgStar Λ (P + Q) * sgStar Λ (P - Q) =
      (wpF Λ Q - wpF Λ P) * sgStar Λ P ^ 2 * sgStar Λ Q ^ 2 := by
    linear_combination hlaw
  simp only [U1, zero_add, mul_zero, zero_mul, zero_div, zero_sub]
  have hexp : ∀ x : ℂ, Complex.exp x ^ 2 = Complex.exp (2 * x) := by
    intro x; rw [← Complex.exp_nat_mul]; norm_num
  have key : Complex.exp (-(↑Real.pi * (P + Q) * (starRingEnd ℂ) (P + Q) / (2 * ↑(area Λ)))) *
      Complex.exp (-(↑Real.pi * (P - Q) * (starRingEnd ℂ) (P - Q) / (2 * ↑(area Λ)))) =
      Complex.exp (-(↑Real.pi * P * (starRingEnd ℂ) P / (2 * ↑(area Λ)))) ^ 2 *
      Complex.exp (-(↑Real.pi * Q * (starRingEnd ℂ) Q / (2 * ↑(area Λ)))) ^ 2 := by
    rw [hexp, hexp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_add, map_sub]
    ring
  calc _ = (sgStar Λ (P + Q) * sgStar Λ (P - Q)) *
      (Complex.exp (-(↑Real.pi * (P + Q) * (starRingEnd ℂ) (P + Q) / (2 * ↑(area Λ)))) *
      Complex.exp (-(↑Real.pi * (P - Q) * (starRingEnd ℂ) (P - Q) / (2 * ↑(area Λ))))) := by ring
    _ = _ := by rw [hσ, key]; ring

end GlobalTheory
