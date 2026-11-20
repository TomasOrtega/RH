import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusTwistedDivisibility
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LemY.dvd_of_frobenius_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFrobeniusTwistedDivisibility.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.frobenius_twisted_divisibility : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] [CharP S p] [PerfectRing S p] (d : ℕ) (m : WittVector p S) (U : Matrix (Fin d) (Fin d) (WittVector p S)) (Z : Fin d → WittVector p S), m.coeff 0 ≠ 0 → (∀ i, m * WittVector.frobenius (Z i) = WittVector.frobenius m * (U *ᵥ Z) i) → ∀ i, m ∣ Z i := by
  first | exact @GlobalTheory.LemY.dvd_of_frobenius_eq | exact GlobalTheory.LemY.dvd_of_frobenius_eq | (intros; apply GlobalTheory.LemY.dvd_of_frobenius_eq <;> assumption)
