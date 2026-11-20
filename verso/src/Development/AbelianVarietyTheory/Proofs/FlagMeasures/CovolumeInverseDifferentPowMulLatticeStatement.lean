import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeInverseDifferentPowMulLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCovolumeInverseDifferentPowMulLattice.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.covolume_inverseDifferentPow_mul_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * dInv E t') c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  first | exact @GlobalTheory.SnMass.VolN.CovMul.hasDom_ideLat_dInv_mul | exact GlobalTheory.SnMass.VolN.CovMul.hasDom_ideLat_dInv_mul | (intros; apply GlobalTheory.SnMass.VolN.CovMul.hasDom_ideLat_dInv_mul <;> assumption)
