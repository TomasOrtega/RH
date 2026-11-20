import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomEqCanonical
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.padicToO_unique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPadicRingHomEqCanonical.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.padic_ring_hom_eq_canonical : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (g : ℤ_[p] →+* O), g = padicToO p O := by
  first | exact @GlobalTheory.padicToO_unique | exact GlobalTheory.padicToO_unique | (intros; apply GlobalTheory.padicToO_unique <;> assumption)
