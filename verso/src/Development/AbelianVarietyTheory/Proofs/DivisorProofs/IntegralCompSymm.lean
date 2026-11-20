import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerToCoinvIffInvFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagCoIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantLinOm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import GroundTheory.AutomorphicForms.MeasuresModulus

noncomputable section

open MeasureTheory
open scoped Matrix Pointwise NNReal

namespace GlobalTheory.ChangeVarPi

/- English proof (translation)
Establish `hc : Continuous M.symm` using `(M.symm : (ι → k) →ₗ[k] (ι → k)).continuous_on_pi`. Use extensionality with `s hs`. Rewrite using `[Measure.map_apply hc.measurable hs, Measure.smul_apply, ← GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq, ENNReal.smul_def, smul_eq_mul, distribHaarChar_mul μ M s]`. Establish `: (M.symm : (ι → k) → (ι → k)) ⁻¹' s = M • s`. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨M.symm x, h, by simp [LinearEquiv.smul_def]⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Simplify `hy` using `[LinearEquiv.smul_def]`. Rewrite using `[this]`.
-/
theorem map_symm_eq_smul (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ι : Type) [Fintype ι]
    (μ : Measure (ι → k)) [μ.IsAddHaarMeasure] (M : (ι → k) ≃ₗ[k] (ι → k)) :
    μ.map M.symm = (distribHaarChar k (LinearEquiv.det M)) • μ := by
  classical
  have hc : Continuous M.symm := (M.symm : (ι → k) →ₗ[k] (ι → k)).continuous_on_pi
  ext s hs
  rw [Measure.map_apply hc.measurable hs, Measure.smul_apply, ← GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq,
    ENNReal.smul_def, smul_eq_mul, distribHaarChar_mul μ M s]
  have : (M.symm : (ι → k) → (ι → k)) ⁻¹' s = M • s := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · intro h
      exact ⟨M.symm x, h, by simp [LinearEquiv.smul_def]⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [LinearEquiv.smul_def] using hy
  rw [this]

end GlobalTheory.ChangeVarPi
