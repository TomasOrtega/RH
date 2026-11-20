import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqLogDerivationExtendLocalizationAw
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLAlgebraMap
open GlobalTheory.LogDerProj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPowSmulEqLogDerivationExtendLocalizationAw.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_pow_smul_eq_logDerivation_extend_localizationAway : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R) (n : (logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S))).restrictScalars R), ∃ x : logSub φ J × Submonoid.powers f, x.2 • n = res (S := S) f φ J x.1 := by
  first | exact @GlobalTheory.LogDerProj.exists_pow_smul_eq_res | exact GlobalTheory.LogDerProj.exists_pow_smul_eq_res | (intros; apply GlobalTheory.LogDerProj.exists_pow_smul_eq_res <;> assumption)
