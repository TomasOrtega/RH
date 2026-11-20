import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpWindowAndBlockExponentOfEmbeddings
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FJumpWindowAndBlockExponentOfEmbeddings.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.jumpWindow_and_blockExponent_of_embeddings : ∀ (S : LocalSituation.Sit) (Y : LocLat S.G S.Qp S.LL S.O) (h r n t : ℕ) [CharZero S.Qp] [FiniteDimensional S.Qp S.K], S.W.s = 1 → Nat.card (S.K →ₐ[S.Qp] S.LL) = finrank S.Qp S.K → finrank S.Qp S.K ≤ n → LocalSituation.gK S = 0 → LocalSituation.vdegMs S (LocalSituation.mN (LocalSituation.ell S) 1 (h + h)) = LocalSituation.mN (LocalSituation.ell S) 1 (h + h) - 1 → t ≤ h → (∀ τ : S.K →ₐ[S.Qp] S.LL, ∃ U : Finset ℤ, U.card ≤ r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u + 1 ≤ h) ∧ ∀ a, IsJumpV S.PD Y.ρ τ a → a ∈ U) → (∀ a ∈ LocalSituation.Jset S Y, -(h : ℤ) ≤ a ∧ a ≤ h) ∧ ∀ e < t, LocalSituation.cTBY S Y h h e ≤ cBnum (LocalSituation.ell S) h t (n * r) := by
  first | exact @GlobalTheory.HubLoc.window_and_cTB_of_jumps_at_embeddings | exact GlobalTheory.HubLoc.window_and_cTB_of_jumps_at_embeddings | (intros; apply GlobalTheory.HubLoc.window_and_cTB_of_jumps_at_embeddings <;> assumption)
