import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormCombinationEqZeroIndependent
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MvPolynomial GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHomogeneousFormCombinationEqZeroIndependent.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.homogeneousFormCombination_eq_zero_independent : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) → AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K → ∀ (ι : Type) [Fintype ι] (g : ι → K), LinearIndependent (ratF x) g → ∀ (q : ℕ) (T : ι → MvPolynomial (Fin (D + 1)) ℤ), (∀ i, (T i).IsHomogeneous q) → ∑ i, aeval x (T i) * g i = 0 → T = 0 := by
  first | exact @GlobalTheory.HSAmp.homogComb_eq_zero | exact GlobalTheory.HSAmp.homogComb_eq_zero | (intros; apply GlobalTheory.HSAmp.homogComb_eq_zero <;> assumption)
