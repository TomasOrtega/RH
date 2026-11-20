import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatKernelTraceIntegrable
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeatKernelTraceIntegrable.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.heat_kernel_trace_integrable : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g m : ℕ} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ} {h : Pt E g → ℝ} (β : Fin m → E) (b : E) (u : ℝ) (D : Set (Fl g)), IsLat M → IsAddFundamentalDomain M D volume → ∀ (K : ℝ → (Fin g → ℂ) → (Fin g → ℂ) → Ext (m + m + g) →L[ℂ] Ext (m + m + g)), IsHeatKernel τ M j h β b u D K → IntegrableOn (fun x => strN (K 1 (per (τ b) x) (per (τ b) x))) D := by
  first | exact @GlobalTheory.integrableOn_strN_heatKernel_diag | exact GlobalTheory.integrableOn_strN_heatKernel_diag | (intros; apply GlobalTheory.integrableOn_strN_heatKernel_diag <;> assumption)
