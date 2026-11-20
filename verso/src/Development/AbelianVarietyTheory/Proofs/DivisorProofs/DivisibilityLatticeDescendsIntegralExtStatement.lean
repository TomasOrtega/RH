import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisibilityLatticeDescendsIntegralExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
open GlobalTheory.RingChain GlobalTheory.PerfdLat
open scoped TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RingChain.dvd_descends_of_isIntegral` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDivisibilityLatticeDescendsIntegralExt.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.divisibility_lattice_descends_integral_ext : ∀ (A' B : Type) [CommRing A'] [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B] [IsDomain B] (g : A' →+* B), Function.Injective g → g.IsIntegral → (∀ a x : A', a ≠ 0 → g a ∣ g x → a ∣ x) ∧ ∀ (h : ℕ) (a : A'), a ≠ 0 → ∀ x : Fin h → A', piMap g (Fin h) x ∈ baseOf (g a) h ↔ x ∈ baseOf a h := by
  first | exact @GlobalTheory.RingChain.dvd_descends_of_isIntegral | exact GlobalTheory.RingChain.dvd_descends_of_isIntegral | (intros; apply GlobalTheory.RingChain.dvd_descends_of_isIntegral <;> assumption)
