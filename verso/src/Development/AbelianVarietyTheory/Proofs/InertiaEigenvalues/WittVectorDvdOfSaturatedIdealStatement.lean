import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorDvdOfSaturatedIdeal
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.wittVector_dvd_of_saturated_ideal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWittVectorDvdOfSaturatedIdeal.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.wittVector_dvd_of_mem_saturated_ideal : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (J : Ideal (WittVector l R)) (μ : WittVector l R), μ ∈ J → (∀ a, (l : WittVector l R) * a ∈ J → a ∈ J) → (∀ a ∈ J, μ.coeff 0 ∣ a.coeff 0) → ∀ a ∈ J, μ ∣ a := by
  first | exact @GlobalTheory.wittVector_dvd_of_saturated_ideal | exact GlobalTheory.wittVector_dvd_of_saturated_ideal | (intros; apply GlobalTheory.wittVector_dvd_of_saturated_ideal <;> assumption)
