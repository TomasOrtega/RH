import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnFinsetLinear
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSuperconnFinsetLinear.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.superconn_finset_linear : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ} (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) {ι : Type} (s : Finset ι) (a : ι → ℂ) (F : ι → Pt E g → Ext (n + n + g)) (P : Pt E g), (∀ i ∈ s, DifferentiableAt ℝ (F i) P) → superconn τ h β u (fun Q => ∑ i ∈ s, a i • F i Q) P = ∑ i ∈ s, a i • superconn τ h β u (F i) P := by
  first | exact @GlobalTheory.superconn_linear | exact GlobalTheory.superconn_linear | (intros; apply GlobalTheory.superconn_linear <;> assumption)
