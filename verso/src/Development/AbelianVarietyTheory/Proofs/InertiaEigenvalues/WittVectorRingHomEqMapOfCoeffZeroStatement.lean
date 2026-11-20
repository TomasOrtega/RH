import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorRingHomEqMapOfCoeffZero
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WittMapUniq.eq_map_of_coeff_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FWittVectorRingHomEqMapOfCoeffZero.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.wittVector_ringHom_eq_map_of_coeff_zero : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] [PerfectRing O l] (F : WittVector l R →+* WittVector l O) (ψ : R →+* O), (∀ a, (F a).coeff 0 = ψ (a.coeff 0)) → F = WittVector.map ψ := by
  first | exact @GlobalTheory.WittMapUniq.eq_map_of_coeff_zero | exact GlobalTheory.WittMapUniq.eq_map_of_coeff_zero | (intros; apply GlobalTheory.WittMapUniq.eq_map_of_coeff_zero <;> assumption)
