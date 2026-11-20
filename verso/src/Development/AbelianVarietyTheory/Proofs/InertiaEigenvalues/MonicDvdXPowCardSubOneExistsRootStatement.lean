import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonicDvdXPowCardSubOneExistsRoot
import Mathlib
open Polynomial IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMonicDvdXPowCardSubOneExistsRoot.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_root_of_monic_dvd_X_pow_card_sub_one : ∀ (S : Type) [CommRing S] [HenselianLocalRing S] [Finite (ResidueField S)] (f : S[X]), f.Monic → f.natDegree ≠ 0 → f ∣ X ^ (Nat.card (ResidueField S) - 1) - 1 → ∃ y : S, f.eval y = 0 := by
  first | exact @GlobalTheory.monic_dvd_X_pow_card_sub_one_exists_root | exact GlobalTheory.monic_dvd_X_pow_card_sub_one_exists_root | (intros; apply GlobalTheory.monic_dvd_X_pow_card_sub_one_exists_root <;> assumption)
