import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHolomorphicRootUpperHalfPlaneOfOrderDvd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open Matrix GlobalTheory.KZ
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RootHs.rootHs` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsHolomorphicRootUpperHalfPlaneOfOrderDvd.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.exists_holomorphic_root_upperHalfPlane_of_order_dvd : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs → (∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt h τ = (k : WithTop ℤ) → (m : ℤ) ∣ k) → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Hs ∧ ∀ z ∈ Hs, g z ^ m = h z := by
  first | exact @GlobalTheory.RootHs.rootHs | exact GlobalTheory.RootHs.rootHs | (intros; apply GlobalTheory.RootHs.rootHs <;> assumption)
