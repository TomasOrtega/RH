import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfSupPowEqOfAdicCompatibleIdeals
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIInfSupPowEqOfAdicCompatibleIdeals.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.iInf_sup_pow_eq_of_adic_compatible_ideals : ∀ (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C → ∀ u : ℕ → Ideal C, (∀ e, u e = u (e + 1) ⊔ J ^ (e + 1)) → ∀ e, (⨅ l, u l) ⊔ J ^ (e + 1) = u e := by
  first | exact @GlobalTheory.iInf_sup_pow_eq_of_compatible | exact GlobalTheory.iInf_sup_pow_eq_of_compatible | (intros; apply GlobalTheory.iInf_sup_pow_eq_of_compatible <;> assumption)
