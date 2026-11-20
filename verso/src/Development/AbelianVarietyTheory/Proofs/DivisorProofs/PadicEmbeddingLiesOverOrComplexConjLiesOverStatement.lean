import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicEmbeddingLiesOverOrComplexConjLiesOver
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
open GlobalTheory.LKTrip
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTGroupOver.liesOver_or_conj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPadicEmbeddingLiesOverOrComplexConjLiesOver.lean&line=103#L103)
-/
theorem _root_.GlobalTheory.T.padicEmbedding_liesOver_or_complexConj_liesOver : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (τ : G.F →+* PadicAlgCl p), LiesOver G.Kq G.u τ ∨ LiesOver G.Kq G.u (τ.comp (conjQ G.F).toRingHom) := by
  first | exact @GlobalTheory.HTGroupOver.liesOver_or_conj | exact GlobalTheory.HTGroupOver.liesOver_or_conj | (intros; apply GlobalTheory.HTGroupOver.liesOver_or_conj <;> assumption)
