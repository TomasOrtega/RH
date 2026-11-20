import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteQuotientOfIsLatLe
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finite_quotient_of_isLat_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteQuotientOfIsLatLe.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.finite_quotient_of_isLat_le' : ∀ {g : ℕ} (M M' : Submodule ℤ (Fl g)), IsLat M → IsLat M' → M ≤ M' → Finite (↥M' ⧸ M.submoduleOf M') := by
  first | exact @GlobalTheory.finite_quotient_of_isLat_le | exact GlobalTheory.finite_quotient_of_isLat_le | (intros; apply GlobalTheory.finite_quotient_of_isLat_le <;> assumption)
