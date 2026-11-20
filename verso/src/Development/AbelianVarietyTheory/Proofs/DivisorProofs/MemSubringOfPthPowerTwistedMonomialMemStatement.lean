import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubringOfPthPowerTwistedMonomialMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
open GlobalTheory GlobalTheory.LogDR

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LogDR.round_coeff_mem` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMemSubringOfPthPowerTwistedMonomialMem.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.mem_subring_of_pthPower_twisted_monomial_mem : ∀ (K : Type) [Field K] (p : ℕ) (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (I J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ) (g : K), 0 < p → AlgChart A x → (∀ j, r j < p) → g ^ p * ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) / ∏ j ∈ I \ J, (x j : K) ∈ A → g * t / ∏ j ∈ I \ J, (x j : K) ∈ A := by
  first | exact @GlobalTheory.LogDR.round_coeff_mem | exact GlobalTheory.LogDR.round_coeff_mem | (intros; apply GlobalTheory.LogDR.round_coeff_mem <;> assumption)
