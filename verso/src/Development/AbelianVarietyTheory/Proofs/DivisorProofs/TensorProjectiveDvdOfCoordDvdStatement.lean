import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProjectiveDvdOfCoordDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTensorProjectiveDvdOfCoordDvd.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_eq_smul_of_dvd_dualDistrib : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] [Module.Projective O M] [Module.Projective O N] (a : O) (z : M ⊗[O] N), (∀ (φ : Module.Dual O M) (ψ : Module.Dual O N), a ∣ TensorProduct.dualDistrib O M N (φ ⊗ₜ ψ) z) → ∃ y, z = a • y := by
  first | exact @GlobalTheory.tensor_projective_dvd_of_coord_dvd | exact GlobalTheory.tensor_projective_dvd_of_coord_dvd | (intros; apply GlobalTheory.tensor_projective_dvd_of_coord_dvd <;> assumption)
