import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissiblePlacesContainingPrimeSupersetMon
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CNorm.exists_admissiblePlaces_superset_and_mono` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FExistsAdmissiblePlacesContainingPrimeSupersetMon.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_admissiblePlacesContainingPrime_superset_mono : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F], 0 < p → (∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∃ S, S₀ ⊆ S ∧ AdmP p F S) ∧ ∀ S T : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T → AdmP p F S → AdmP p F T := by
  first | exact @GlobalTheory.CNorm.exists_admissiblePlaces_superset_and_mono | exact GlobalTheory.CNorm.exists_admissiblePlaces_superset_and_mono | (intros; apply GlobalTheory.CNorm.exists_admissiblePlaces_superset_and_mono <;> assumption)
