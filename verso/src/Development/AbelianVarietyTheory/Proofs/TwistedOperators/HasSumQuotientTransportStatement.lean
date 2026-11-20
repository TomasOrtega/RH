import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumQuotientTransport
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.hasSum_quotient_transport` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FHasSumQuotientTransport.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient : ∀ (G H : Type) [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) (K' : Subgroup H), (∀ g, g ∈ K ↔ e g ∈ K') → ∀ f : G → ℂ, (∀ g, ∀ k ∈ K, f (g * k) = f g) → ∀ s : ℂ, HasSum (fun b : H ⧸ K' => f (e.symm b.out)) s → HasSum (fun a : G ⧸ K => f a.out) s := by
  first | exact @GlobalTheory.hasSum_quotient_transport | exact GlobalTheory.hasSum_quotient_transport | (intros; apply GlobalTheory.hasSum_quotient_transport <;> assumption)
