import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicConjInvariantEqSumInducedDerivatives
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMirabolicConjInvariantEqSumInducedDerivatives.lean&line=110#L110)
-/
theorem _root_.GlobalTheory.T.mirabolicConjInvariant_eq_sum_induced_derivatives : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (n : ℕ) (F : Gn g n → ℂ), 1 ≤ n → IsMirClass F → ∀ p : Gn g n, InMir (p : Mt g n) → F p = ∑ i ∈ Finset.range n, indR ψ i n (der ψ i F) p := by
  first | exact @GlobalTheory.GLm.MirSum.eq_sum_indR_der | exact GlobalTheory.GLm.MirSum.eq_sum_indR_der | (intros; apply GlobalTheory.GLm.MirSum.eq_sum_indR_der <;> assumption)
