import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSkewTraceEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Matrix GlobalTheory.SUCong
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCardSkewTraceEq.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.card_skew_trace_eq : ∀ {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (S : Subring A) (σ : A →+* A) (H : Matrix n n A) (ϖ : A) (q : ℕ), GoodRing S σ ϖ q → GoodForm S σ H → Nat.card (skewTr S σ H ϖ) = q ^ (Fintype.card n ^ 2 - 1) := by
  first | exact @GlobalTheory.SUCong.card_skewTr | exact GlobalTheory.SUCong.card_skewTr | (intros; apply GlobalTheory.SUCong.card_skewTr <;> assumption)
