import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ClassMeanPeriods
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JacobiThetaHalfCharacteristic
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanLogPeriodConjugatesEqChowlaSelberg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.MeanLogArea

/- English proof (translation)
Introduce `D cc δ M _ t hS`. Take `⟨hcc, hδ, hM, -⟩` from `hS`. Establish `hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ` using `⟨hcc, hδ⟩`. Establish `hmean` using `GlobalTheory.PeriodMean.mean_log_period D (GlobalTheory.InducedType.induced_type D).1 cc δ hc M hM.2.1 hM.2.2`. Establish `hpos : ∀ ρ : M →ₐ[ℚ] ℂ, 0 < area (lamConj M ρ (lamOf D cc δ))` using `fun ρ => GlobalTheory.Glob.area_lamConj_pos hc hM ρ`.

Establish `hcard : (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) = (Module.finrank ℚ M : ℝ)`. Conclude with `AlgHom.card ℚ M ℂ` after adjusting the coercions. Establish `hn : (Module.finrank ℚ M : ℝ) ≠ 0`. Conclude with `(Module.finrank_pos (R := ℚ) (M := M)).ne'` after adjusting the coercions. Establish `hsplit : (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) = (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)) / Real.pi)) + (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) * Real.log Real.pi`.

Rewrite using `[← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Rewrite using `[Real.log_div (hpos ρ).ne' Real.pi_pos.ne']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit, add_div, hcard, mul_div_cancel_left₀ _ hn]`.

Unfold `ClassMeanPeriods.classMeanValue`. Rewrite using `[hmean]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mean_log_area : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) / (Module.finrank ℚ M : ℝ) = Real.log Real.pi + ClassMeanPeriods.classMeanValue D := by
  intro D cc δ M _ t hS
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hmean := GlobalTheory.PeriodMean.mean_log_period D (GlobalTheory.InducedType.induced_type D).1 cc δ hc M
    hM.2.1 hM.2.2
  have hpos : ∀ ρ : M →ₐ[ℚ] ℂ, 0 < area (lamConj M ρ (lamOf D cc δ)) :=
    fun ρ => GlobalTheory.Glob.area_lamConj_pos hc hM ρ
  have hcard : (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) = (Module.finrank ℚ M : ℝ) := by
    exact_mod_cast AlgHom.card ℚ M ℂ
  have hn : (Module.finrank ℚ M : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := M)).ne'
  have hsplit : (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) =
      (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)) / Real.pi)) +
        (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) * Real.log Real.pi := by
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Real.log_div (hpos ρ).ne' Real.pi_pos.ne']
    ring
  rw [hsplit, add_div, hcard, mul_div_cancel_left₀ _ hn]
  unfold ClassMeanPeriods.classMeanValue
  rw [hmean]
  ring

end GlobalTheory.MeanLogArea
