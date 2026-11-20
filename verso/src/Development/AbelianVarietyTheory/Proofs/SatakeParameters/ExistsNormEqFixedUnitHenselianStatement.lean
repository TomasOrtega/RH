import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqFixedUnitHenselian
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HenselianNorm.exists_norm_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsNormEqFixedUnitHenselian.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.exists_norm_eq_fixed_unit_henselian : ∀ (R : Type) [CommRing R] (I : Ideal R) [HenselianRing R I] [Finite (R ⧸ I)] (c : R →+* R), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) → (∃ ω, IsUnit (ω - c ω)) → ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u := by
  first | exact @GlobalTheory.HenselianNorm.exists_norm_eq | exact GlobalTheory.HenselianNorm.exists_norm_eq | (intros; apply GlobalTheory.HenselianNorm.exists_norm_eq <;> assumption)
