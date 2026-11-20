import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaDegBotEqFinrankFiniteDomain
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.inertiaDeg_bot_eq_finrank` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FInertiaDegBotEqFinrankFiniteDomain.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.inertiaDeg_bot_eq_finrank_finite_domain : ∀ (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S], Function.Injective (algebraMap R S) → (⊥ : Ideal S).inertiaDeg R = Module.finrank R S := by
  first | exact @GlobalTheory.inertiaDeg_bot_eq_finrank | exact GlobalTheory.inertiaDeg_bot_eq_finrank | (intros; apply GlobalTheory.inertiaDeg_bot_eq_finrank <;> assumption)
