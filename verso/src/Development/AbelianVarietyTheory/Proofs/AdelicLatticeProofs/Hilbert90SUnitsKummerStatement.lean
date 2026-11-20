import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90SUnitsKummer
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CNorm.hilbert90_sUnits_kummer` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FHilbert90SUnitsKummer.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.hilbert90_sUnits_kummer' : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → AdmP p F S → (∀ v, v ∉ S → v.valuation F δ = 1) → ∀ u : Eˣ, u ∈ sUnits E SE → ∏ i ∈ Finset.range p, σ^[i] (u : E) = 1 → ∃ y : Eˣ, y ∈ sUnits E SE ∧ (u : E) = σ y / y := by
  first | exact @GlobalTheory.CNorm.hilbert90_sUnits_kummer | exact GlobalTheory.CNorm.hilbert90_sUnits_kummer | (intros; apply GlobalTheory.CNorm.hilbert90_sUnits_kummer <;> assumption)
